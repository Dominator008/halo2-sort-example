use crate::less_than::{LtChip, LtConfig, LtInstruction};
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Layouter, SimpleFloorPlanner},
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, Instance, Selector,
    },
    poly::Rotation,
};
use std::marker::PhantomData;

const NUM_ELEMENTS: usize = 4;
const NUM_BYTES: usize = 8;

#[derive(Debug, Clone)]
struct SortNConfig<F: FieldExt> {
    // N inputs, N outputs
    pub advice: [Column<Advice>; 2 * NUM_ELEMENTS],
    pub master_selector: Selector,
    pub instance: Column<Instance>,

    lt_selectors: [Selector; NUM_ELEMENTS - 1],
    lt_configs: [LtConfig<F, NUM_BYTES>; NUM_ELEMENTS - 1],
}

#[derive(Debug, Clone)]
struct SortNChip<F: FieldExt> {
    config: SortNConfig<F>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> SortNChip<F> {
    pub fn construct(config: SortNConfig<F>) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(
        meta_cs: &mut ConstraintSystem<F>,
        advice: [Column<Advice>; 2 * NUM_ELEMENTS],
        instance: Column<Instance>,
        fixed: Column<Fixed>,
    ) -> SortNConfig<F> {
        meta_cs.enable_equality(instance);
        meta_cs.enable_constant(fixed);
        for column in &advice {
            meta_cs.enable_equality(*column);
        }
        let master_selector = meta_cs.selector();
        let mut lt_selectors = Vec::with_capacity(NUM_ELEMENTS - 1);
        for _i in 0..NUM_ELEMENTS - 1 {
            lt_selectors.push(meta_cs.selector());
        }

        let mut lt_configs = Vec::with_capacity(NUM_ELEMENTS - 1);
        let mut advice_vec = advice.to_vec();
        for _i in 0..NUM_BYTES + 1 - 2 * NUM_ELEMENTS {
            advice_vec.push(meta_cs.advice_column());
        }
        let mut diff = Vec::with_capacity(NUM_BYTES);
        for i in 1..NUM_BYTES + 1 {
            diff.push(advice_vec[i]);
        }
        for i in 0..NUM_ELEMENTS - 1 {
            let lt_config: LtConfig<F, NUM_BYTES> = LtChip::configure(
                meta_cs,
                |meta| meta.query_selector(lt_selectors[i]),
                |meta| meta.query_advice(advice_vec[i], Rotation(-1 - i as i32)),
                |meta| meta.query_advice(advice_vec[i + 1], Rotation(-1 - i as i32)),
                advice_vec[0],
                diff.clone().try_into().unwrap(),
            );
            lt_configs.push(lt_config);
        }

        let mut lt_constraints = Vec::with_capacity(NUM_ELEMENTS - 1);
        meta_cs.create_gate("sortN", |meta_vc| {
            //  0 |  1 |  2 |  3 |  4 |  5 |  6 |  7 | selectors
            // i0   i1   i2   i3   o0   o1   o2   o3
            // o0'  o1'  o2'  o3'
            // lt0 diff0_0-7
            // lt1 diff1_0-7
            // lt2 diff2_0-7
            let s = meta_vc.query_selector(master_selector);

            for i in 0..NUM_ELEMENTS - 1 {
                lt_constraints.push(
                    s.clone()
                        * (lt_configs[i].is_lt(meta_vc, Some(Rotation(i as i32 + 2)))
                            - Expression::Constant(F::one())),
                );
            }
            lt_constraints
        });

        SortNConfig {
            advice,
            master_selector,
            instance,
            lt_configs: lt_configs.try_into().unwrap(),
            lt_selectors: lt_selectors.try_into().unwrap(),
        }
    }

    #[allow(clippy::type_complexity)]
    pub fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        in_indices: [usize; NUM_ELEMENTS],
        values: [F; NUM_ELEMENTS],
    ) -> Result<[AssignedCell<F, F>; NUM_ELEMENTS], Error> {
        layouter.assign_region(
            || "sort",
            |mut region| {
                self.config.master_selector.enable(&mut region, 0)?;

                // unsorted inputs
                let mut in_cells = Vec::with_capacity(2 * NUM_ELEMENTS);
                for (i, column) in self.config.advice.iter().enumerate() {
                    in_cells.push(region.assign_advice_from_instance(
                        || format!("instance({})", i),
                        self.config.instance,
                        i,
                        *column,
                        0,
                    )?);
                }

                // sorted outputs
                let mut output_cells = Vec::with_capacity(NUM_ELEMENTS);
                for i in 0..NUM_ELEMENTS {
                    output_cells.push(in_cells[in_indices[i]].copy_advice(
                        || format!("sort out[{}]", i),
                        &mut region,
                        self.config.advice[i],
                        1,
                    )?);
                }

                // lt chips
                for i in 0..NUM_ELEMENTS - 1 {
                    self.config.lt_selectors[i].enable(&mut region, i + 2)?;
                }
                let mut results = Vec::with_capacity(NUM_ELEMENTS - 1);
                for i in 0..NUM_ELEMENTS - 1 {
                    let lt_chip = LtChip::construct(self.config.lt_configs[i]);
                    results.push(lt_chip.assign(&mut region, i + 2, values[i], values[i + 1]));
                }
                Ok(output_cells.try_into().unwrap())
            },
        )
    }

    pub fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        cell: &AssignedCell<F, F>,
        row: usize,
    ) -> Result<(), Error> {
        layouter.constrain_instance(cell.cell(), self.config.instance, row)
    }
}

#[derive(Default)]
struct SortNCircuit<F> {
    values: [F; NUM_ELEMENTS],
    _marker: PhantomData<F>,
}

impl<F: FieldExt> Circuit<F> for SortNCircuit<F> {
    type Config = SortNConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let mut advice = Vec::with_capacity(2 * NUM_ELEMENTS);
        for _i in 0..2 * NUM_ELEMENTS {
            advice.push(meta.advice_column());
        }
        let instance = meta.instance_column();
        let fixed = meta.fixed_column();
        SortNChip::configure(meta, advice.try_into().unwrap(), instance, fixed)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let chip = SortNChip::construct(config);

        // Bubble sort, keeping track of indices
        let mut in_indices = [0; NUM_ELEMENTS];
        for i in 0..NUM_ELEMENTS {
            in_indices[i] = i;
        }
        let mut values = self.values;
        for i in 1..NUM_ELEMENTS {
            for j in 1..(NUM_ELEMENTS - i + 1) {
                if values[j] < values[j - 1] {
                    values.swap(j - 1, j);
                    in_indices.swap(j - 1, j);
                }
            }
        }

        let output_cells = chip.assign(layouter.namespace(|| "all"), in_indices, values)?;

        for i in 0..NUM_ELEMENTS {
            chip.expose_public(
                layouter.namespace(|| "out"),
                &output_cells[i],
                i + NUM_ELEMENTS,
            )?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::marker::PhantomData;

    use super::SortNCircuit;
    use halo2_proofs::{dev::MockProver, pasta::Fp};

    #[test]
    fn sort_n_example() {
        let k = 4;

        let ins = [Fp::from(3), Fp::from(1), Fp::from(4), Fp::from(2)];
        let outs = [Fp::from(1), Fp::from(2), Fp::from(3), Fp::from(4)];

        let circuit = SortNCircuit {
            values: ins,
            _marker: PhantomData,
        };

        let mut public_input = vec![
            ins[0], ins[1], ins[2], ins[3], outs[0], outs[1], outs[2], outs[3],
        ];
        let prover = MockProver::run(k, &circuit, vec![public_input.clone()]).unwrap();
        prover.assert_satisfied();

        // Change instances to [3, 1, 4, 2, 2, 1, 3, 4]
        public_input[4] += Fp::one();
        public_input[5] -= Fp::one();
        let _prover = MockProver::run(k, &circuit, vec![public_input]).unwrap();
        // uncomment the following line and the assert will fail
        // _prover.assert_satisfied();
    }

    #[cfg(feature = "dev-graph")]
    #[test]
    fn plot_sort_n() {
        use plotters::prelude::*;

        let root = BitMapBackend::new("sort-n-layout.png", (1024, 3096)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root.titled("Sort N Layout", ("sans-serif", 60)).unwrap();

        let ins = [Fp::from(3), Fp::from(1), Fp::from(4), Fp::from(2)];
        let circuit = SortNCircuit::<Fp> {
            values: ins,
            _marker: PhantomData,
        };
        halo2_proofs::dev::CircuitLayout::default()
            .render(4, &circuit, &root)
            .unwrap();
    }
}
