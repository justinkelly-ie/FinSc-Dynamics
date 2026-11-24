# FinSc-Dynamics

**Layer 2 blind local evolution over [`FinSc-Box`](https://github.com/justinkelly-ie/FinSc-Box) — zero observer state, zero grid walls, and zero background clock.**

`FinSc-Dynamics` sits directly between core multiset algebra (`FinSc-Box`) and pluggable observer libraries (`FinSc-Lens`, `FinSc-Dihedron`):

```text
                FinSc-Box               (Layer 1: Core Multiset & Maxel Algebra)
                    │
                    ▼
             FinSc-Dynamics             (Layer 2: Blind Local Evolution — App1, NoThrow)
               ╱         ╲
              ▼           ▼
        FinSc-Lens     FinSc-Dihedron   (Layer 3: Independent Non-Perturbing Observers)
              ╲           ╱
               ▼         ▼
             Finite-Science             (Layer 4: Top-of-Stack Lab, Audits & Visualizer)
```

## Modules

- [`Evolution.idr`](src/FinScDynamics/Evolution.idr) — `Configuration` (`PureMultiset`), `DynamicsParams` (`canonDynamicsParams`), `EvolutionState`, `PolarityMaxel`, `QuadranceMaxel` (`quadranceOf`), `Coord2` & `Coord3` bases, causal 1-hop `loadMaxel`, Bresenham `throttleMaxel`, `seedExcitation`, `seedDirectedPulse`, `seedBoundDipole`, `stepDynamicsWith`, `stepCoupledSourceFlow`, and `stepCoupledUniversePair`.
- [`FlatUniverse.idr`](src/FinScDynamics/FlatUniverse.idr) — Polymorphic linear `App1` `FlatBlackBox k` (`FlatBlackBox Coord2`, `FlatBlackBox Coord3`).
- [`HereditaryUniverse.idr`](src/FinScDynamics/HereditaryUniverse.idr) — 5-shape zero-tag `Configuration` root codec (`mkLoadKey`, `mkThrottleKey`, `mkLocalizedKey`) and linear `App1` `HereditaryBlackBox` with observer-agnostic `observeHereditaryPure`.

## Building & Installing

```bash
cd FinSc-Box && idris2 --build FinSc-Box.ipkg && idris2 --install FinSc-Box.ipkg
cd ../FinSc-Dynamics && idris2 --build FinSc-Dynamics.ipkg && idris2 --install FinSc-Dynamics.ipkg
```

## License

Released under the MIT License.
