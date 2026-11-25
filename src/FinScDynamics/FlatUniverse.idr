module FinScDynamics.FlatUniverse

import Control.App
import FinScBox.BoxInt
import FinScBox.Lenses
import FinScDynamics.Evolution

%default total

--------------------------------------------------------------------------------
-- 1. MODEL A: POLYMORPHIC CLOSED 0D SPARSE FIELD COMPUTE (`App1`, `NoThrow`)
--    - Parameterized over any discrete coordinate basis `k` (`SignedCoord` 1D, `Coord2` 2D, `Coord3` 3D).
--    - Evolves blindly with zero walls, zero observer state, and zero display/codec dependencies.
--------------------------------------------------------------------------------

export
data FlatBlackBox : (k : Type) -> Type where
  MkFlatBox : (basis : AxisBasis k) -> (state : EvolutionState k) -> FlatBlackBox k

--------------------------------------------------------------------------------
-- 2. CLOSED LINEAR `App1` COMPUTE & NON-PERTURBING `PureObservation` TAP
--------------------------------------------------------------------------------

||| Boots Model A cleanly from the 0D vacuum root `[]` over any coordinate `AxisBasis k`.
export
bootFlatWith : AxisBasis k -> App1 e (FlatBlackBox k)
bootFlatWith basis = App1.pure1 (MkFlatBox basis emptyEvolutionState)

||| Splits a balanced dipole `+weight` at `posA` and `-weight` at `posB` directly over native coordinates `k`.
export
splitFlatFromVacuum :
  Ord k =>
  (posA, posB : k) ->
  (weight     : BoxInt) ->
  (1 u        : FlatBlackBox k) ->
  App1 e (FlatBlackBox k)
splitFlatFromVacuum posA posB weight (MkFlatBox basis state) =
  App1.pure1 (MkFlatBox basis (state <+> seedDipoleSites posA posB weight))

||| Superposes an arbitrary balanced zero-sum `EvolutionState k` directly into Model A.
export
injectFlatState :
  Ord k =>
  EvolutionState k ->
  (1 u : FlatBlackBox k) ->
  App1 e (FlatBlackBox k)
injectFlatState delta (MkFlatBox basis state) =
  App1.pure1 (MkFlatBox basis (state <+> delta))

||| Blind local evolution step under explicit `DynamicsParams`.
export
stepFlatWith :
  Ord k =>
  DynamicsParams ->
  (1 u : FlatBlackBox k) ->
  App1 e (FlatBlackBox k)
stepFlatWith params (MkFlatBox basis state) =
  App1.pure1 (MkFlatBox basis (fst (stepDynamicsWith basis params state)))

||| Blind local evolution step under `canonDynamicsParams mode`.
export
stepFlatByMode :
  Ord k =>
  StepMode ->
  (1 u : FlatBlackBox k) ->
  App1 e (FlatBlackBox k)
stepFlatByMode mode = stepFlatWith (canonDynamicsParams mode)

||| Universal non-perturbing external projection on `FlatBlackBox k` carrying `0 same : uOut = uIn`.
export
observeFlatPure :
  (EvolutionState k -> out) ->
  (1 u : FlatBlackBox k) ->
  App1 e (PureObservation u out)
observeFlatPure proj (MkFlatBox basis state) =
  let val = proj state
  in App1.pure1 (MkFlatBox basis state `MkPureObs` val $ Refl)

||| Consumes the linear `FlatBlackBox k` once (`One -> Any`), returning the quenched final `EvolutionState k`.
export
closeFlat0D : (1 u : FlatBlackBox k) -> App1 {u=Any} e (EvolutionState k)
closeFlat0D (MkFlatBox _ state) = App1.pure state
