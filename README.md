# FinSc-Space

**Layer 2 observer-free geometry and blind local evolution over [`FinSc-Box`](https://github.com/justinkelly-ie/FinSc-Box).**

`FinSc-Space` unifies discrete affine/projective geometry with blind local dynamics into a single observer-free layer separated into three directories (`Geometry.Affine`, `Geometry.Projective`, and `Dynamics`), where `Dynamics` imports only `FinSc-Box` and `Geometry.Affine` (never `Geometry.Projective`):

```text
FinSc-Box (Layer 1: Pure Box, HereditaryMSet, Maxel, Space n, GohBound, QuadraticTriple)
    │
    ▼
FinSc-Space (Layer 2: Geometry.{Affine, Projective} + Dynamics)
    │
    ▼
FinSc-Lens (Layer 3: External non-perturbing horizons, projective & frame readouts)
    │
    ▼
Finite-Science (Layer 4: Multi-observer lab & audit suite)
```

## Modules

- [`Geometry/Affine.idr`](src/FinScSpace/Geometry/Affine.idr) — Emergent axis atoms, `AxisBasis k` (`spaceBasis`, `pureMSetBasis`), `quadranceOf`, `SymForm` metric pairings (`blueMetric`, `redMetric`, `greenMetric2`), `archimedesQuadrea`, and universal `QTT 0 Refl` proofs of the Triple Quad Formula and Chromogeometry Three-Fold Quadrea Theorem in `Box BoxInt (Space n)`.
- [`Geometry/Projective.idr`](src/FinScSpace/Geometry/Projective.idr) — Division-free projective `Proportion`, metric-polymorphic `spreadBetween`, universal `QTT 0 Refl` proofs of the Spread Law, Cross Law, and Triple Spread Law, unified metric-parameterized `Rotor` (`SO(3; Q)` Quaternions under `blueMetric` and `SO(1, 2; Q)` Wildberger Dihedrons under `redMetric`), `QuadraticTriple` boosts, Wigner–Thomas precession, and $\mathbb{D} \otimes \mathbb{D}$ `AntisymForm` Quaternion realization.
- [`Dynamics/Evolution.idr`](src/FinScSpace/Dynamics/Evolution.idr) — Frame-blind local quadratic exchange (`EvolutionState`, `DynamicsParams`, causal 1-hop `loadMaxel`, Bresenham `throttleMaxel`, `stepDynamicsWith`, `stepDynamicsStreamWith`, `stepCoupledSourceFlow`, `stepCoupledUniversePair`).
- [`Dynamics/FlatUniverse.idr`](src/FinScSpace/Dynamics/FlatUniverse.idr) — Polymorphic linear `App1` `FlatBlackBox k`.
- [`Dynamics/HereditaryUniverse.idr`](src/FinScSpace/Dynamics/HereditaryUniverse.idr) — Zero-tag `Configuration` root codec and linear `App1` `HereditaryBlackBox`.

## Building & Installing

```bash
cd FinSc-Box && idris2 --build FinSc-Box.ipkg && idris2 --install FinSc-Box.ipkg
cd ../FinSc-Space && idris2 --build FinSc-Space.ipkg && idris2 --install FinSc-Space.ipkg
```

## License

Released under the MIT License.
