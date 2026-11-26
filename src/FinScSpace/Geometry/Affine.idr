module FinScSpace.Geometry.Affine

import FinScBox.BoxInt
import FinScBox.Interfaces
import FinScBox.Box
import FinScBox.HereditaryMSet

%default total

--------------------------------------------------------------------------------
-- 1. TIMELESS CONFIGURATION, EMERGENT AXIS ATOMS & DIRECTED EDGE KEYS
--------------------------------------------------------------------------------

||| Timeless snapshot of a spatial multiset configuration (`PureMultiset`).
public export
Configuration : Type
Configuration = PureMultiset

||| Canonical positive scalar axis atom `{ [] : i + 1 }` (`0 -> X`, `1 -> Y`, `2 -> Z`, ...).
public export
axisAtom : Nat -> PureMultiset
axisAtom i = scalarKeyHMSet (natToInteger (S i))

||| If `k` is a positive scalar axis atom `{ [] : i }` (`i >= 1`), returns `Just i`.
public export
axisAtomIndex : PureMultiset -> Maybe Integer
axisAtomIndex (MkHMSet (BoxNode _ BoxLeaf (MkHMSet BoxLeaf) (MkBoxInt i) BoxLeaf)) =
  if i > 0 then Just i else Nothing
axisAtomIndex _ = Nothing

public export
atomToFin : {n : Nat} -> PureMultiset -> Maybe (Fin n)
atomToFin k =
  case axisAtomIndex k of
    Just i  => natToFin (integerToNat (i - 1)) n
    Nothing => Nothing

||| True iff `k` is an emergent positive scalar axis atom `{ [] : i }` (`i >= 1`).
public export
isAxisAtom : PureMultiset -> Bool
isAxisAtom k =
  case axisAtomIndex k of
    Just _  => True
    Nothing => False

||| True iff every key in `m` is an emergent spatial axis atom `{ [] : i }` (`i >= 1`, including `[]` at the origin).
public export
isSiteKey : PureMultiset -> Bool
isSiteKey (MkHMSet b) = allBox (\k, _ => isAxisAtom k) b

||| Projects any `Configuration` onto its spatial axis-atom components (`isSiteKey`-preserving, signed, ND).
public export
projectToSiteMSet : Configuration -> Configuration
projectToSiteMSet (MkHMSet b) = MkHMSet (filterBox isAxisAtom b)

||| Decodes a single-entry wrapped box `{ k : expectedW }` cleanly without allocation.
public export
extractSignedWrap : BoxInt -> PureMultiset -> Maybe PureMultiset
extractSignedWrap expectedW (MkHMSet (BoxNode _ BoxLeaf k w BoxLeaf)) =
  if w == expectedW then Just k else Nothing
extractSignedWrap _ _ = Nothing

||| Decodes `wrapBox k = { k : +1 }` back to `k`.
public export
extractWrapBox : PureMultiset -> Maybe PureMultiset
extractWrapBox = extractSignedWrap (MkBoxInt 1)

||| Extracts the unique key carrying multiplicity `expectedW` in `b`, or `Nothing` if absent/duplicated.
public export
extractUniqueSlot : BoxInt -> Box BoxInt PureMultiset -> Maybe PureMultiset
extractUniqueSlot expectedW b =
  case foldBox (\k, w, (cnt, res) =>
                  if w == expectedW then (S cnt, Just k) else (cnt, res))
               (0, Nothing) b of
    (1, Just k) => Just k
    _           => Nothing

||| Pure directed-edge key `{ wrapBox posA : +1, wrapBox posB : -1 }` inside `PureMultiset`.
public export
mkEdgeKey : (posA, posB : PureMultiset) -> PureMultiset
mkEdgeKey posA posB =
  MkHMSet $ setBox (wrapBox posB) (MkBoxInt (-1))
          $ singletonBox (wrapBox posA) (MkBoxInt 1)

||| Decoder for pure directed-edge keys `mkEdgeKey posA posB`.
public export
unpackEdgeKey : PureMultiset -> Maybe (PureMultiset, PureMultiset)
unpackEdgeKey entry@(MkHMSet b) =
  if isSiteKey entry || treeSizeNonZero b /= 2
    then Nothing
    else do
      kSrc <- extractUniqueSlot (MkBoxInt 1) b
      kDst <- extractUniqueSlot (MkBoxInt (-1)) b
      a    <- extractWrapBox kSrc
      d    <- extractWrapBox kDst
      if isSiteKey a && isSiteKey d && a /= d then Just (a, d) else Nothing

--------------------------------------------------------------------------------
-- 2. SPARSE COORDINATE BASES (`Space n` & `PureMultiset`)
--------------------------------------------------------------------------------

||| Pure multiset spatial basis shared across `GroupCoord k` coordinates (`Space n` and `PureMultiset`).
public export
record AxisBasis (k : Type) where
  constructor MkAxisBasis
  baseAxes          : Box BoxInt PureMultiset
  allowEmergentAxes : Bool
  axisStep          : PureMultiset -> k
  isOddAxis         : PureMultiset -> k -> Bool
  toSiteMSet        : k -> PureMultiset
  fromSiteMSet      : PureMultiset -> k
  unitAxes          : Box BoxInt k

public export
mkPureCoord : {n : Nat} -> Space n -> Configuration
mkPureCoord =
  foldSpaceWithFin (\i, c, acc => acc <+> scaleM (signedToBoxInt c) (wrapBox (axisAtom (finToNat i)))) emptyHMSet

public export
coordAlong : AxisBasis k -> PureMultiset -> k -> Integer
coordAlong ax axKey pos = unwrapBox (lookupKeyHMSet axKey (ax.toSiteMSet pos))

public export
mkCoord : {n : Nat} -> AxisBasis k -> Space n -> k
mkCoord ax = ax.fromSiteMSet . mkPureCoord

public export
collectSiteAxisAtoms : PureMultiset -> Box BoxInt PureMultiset -> Box BoxInt PureMultiset
collectSiteAxisAtoms (MkHMSet b) acc0 =
  supportBox (acc0 <+> filterBox isAxisAtom b)

||| Unions `ax.baseAxes` with all emergent positive axis atoms `{ [] : i }` present in `pol`.
public export
activeAxisAtomsOf : AxisBasis k -> Maxel BoxInt k k DiagAntisymForm -> Box BoxInt PureMultiset
activeAxisAtomsOf ax pol =
  if not ax.allowEmergentAxes
    then ax.baseAxes
    else foldStoredMaxel
           (\a, b, _, acc =>
              collectSiteAxisAtoms (ax.toSiteMSet b)
                (collectSiteAxisAtoms (ax.toSiteMSet a) acc))
           ax.baseAxes pol

public export
activeUnitAxesOf : GroupCoord k => AxisBasis k -> Maxel BoxInt k k DiagAntisymForm -> Box BoxInt k
activeUnitAxesOf ax pol =
  if not ax.allowEmergentAxes
    then ax.unitAxes
    else
      let atoms = activeAxisAtomsOf ax pol
      in if atoms == ax.baseAxes
           then ax.unitAxes
           else unitStencilBox ax.axisStep atoms

||| Builds an `AxisBasis k` over any `GroupCoord k`.
public export
mkAxisBasis :
  GroupCoord k =>
  (allowEmergent : Bool) ->
  (axes          : Box BoxInt PureMultiset) ->
  (stepFn        : PureMultiset -> k) ->
  (oddFn         : PureMultiset -> k -> Bool) ->
  (toMSet        : k -> PureMultiset) ->
  (fromMSet      : PureMultiset -> k) ->
  AxisBasis k
mkAxisBasis allowEmergent axes stepFn oddFn toMSet fromMSet =
  MkAxisBasis axes allowEmergent stepFn oddFn toMSet fromMSet (unitStencilBox stepFn axes)

public export
baseAxesN : Nat -> Box BoxInt PureMultiset
baseAxesN Z     = BoxLeaf
baseAxesN (S k) = setBox (axisAtom k) (MkBoxInt 1) (baseAxesN k)

||| Dimension-uniform coordinate basis for `Space n` (`1D`, `2D`, `3D`, `ND`).
public export
spaceBasis : {n : Nat} -> AxisBasis (Space n)
spaceBasis {n} =
  mkAxisBasis
    False
    (baseAxesN n)
    (\axKey => maybe (zeroSpace n) unitSpace (atomToFin axKey))
    (\axKey, pos => maybe False (\i => isOddSigned (indexSpace i pos)) (atomToFin axKey))
    mkPureCoord
    (\m => tabulateSpace (\i => cast (lookupKeyHMSet (axisAtom (finToNat i)) m)))

public export
pureMSetBasis : Nat -> AxisBasis PureMultiset
pureMSetBasis dim =
  mkAxisBasis
    True
    (baseAxesN dim)
    wrapBox
    (\axKey, pos => isOddBox (lookupKeyHMSet axKey pos))
    id
    projectToSiteMSet

--------------------------------------------------------------------------------
-- 3. AFFINE DISPLACEMENTS, SYMMETRIC METRIC MAXELS & CHROMOGEOMETRY
--------------------------------------------------------------------------------

||| Free monomial generator `x_i` in the polynomial ring `Box BoxInt (Space n) = Z[x_0, ..., x_{n-1}]`.
public export
polyVar : {n : Nat} -> Fin n -> Box BoxInt (Space n)
polyVar i = singletonBox (unitSpace i) (MkBoxInt 1)

||| Sparse 2-component vector `Box BoxInt (Fin 2)`.
public export
vec2Box : BoxInt -> BoxInt -> Box BoxInt (Fin 2)
vec2Box a b = setBox (FS FZ) b (singletonBox (the (Fin 2) FZ) a)

||| Sparse 3-component vector `Box BoxInt (Fin 3)`.
public export
vec3Box : BoxInt -> BoxInt -> BoxInt -> Box BoxInt (Fin 3)
vec3Box t r s = setBox (FS (FS FZ)) s (setBox (FS FZ) r (singletonBox (the (Fin 3) FZ) t))

||| Converts any `Space n` displacement into a sparse `Box BoxInt (Fin n)`.
public export
spaceToFinBox : {n : Nat} -> Space n -> Box BoxInt (Fin n)
spaceToFinBox = foldSpaceWithFin (\i, c, acc => setBox i (signedToBoxInt c) acc) BoxLeaf

||| Canonical symmetric quadrance `Maxel` (`SymForm`) of `pol : Maxel BoxInt k k DiagAntisymForm`:
||| diagonal `(a, a)` holds `2 * p(a)^2` and off-diagonal `(a, b)` (`a < b`) holds `u_{ab}^2`.
public export
quadranceOf : Ord k => Maxel BoxInt k k DiagAntisymForm -> Maxel BoxInt k k SymForm
quadranceOf pol =
  let pSq = pol .*. pol
  in pSq <+> diagEmbedMaxel (diagBox pSq)

||| Symmetric bilinear dot product `u^T g v` evaluated over any `SymForm` metric `Maxel`.
public export
metricDot : Ord k => Maxel BoxInt k k SymForm -> Box BoxInt k -> Box BoxInt k -> BoxInt
metricDot g u v = u <.> actMaxelR (toGeneralMaxel g) v

||| Metric quadrance `Q_g(v) = v^T g v` over any `SymForm` metric `Maxel`.
public export
metricQuadrance : Ord k => Maxel BoxInt k k SymForm -> Box BoxInt k -> BoxInt
metricQuadrance g v = metricDot g v v

||| 2x2 symmetric Gram `Maxel` of vectors `(u, v)` under metric `g`.
public export
gramMaxel2 : Ord k => Maxel BoxInt k k SymForm -> Box BoxInt k -> Box BoxInt k -> Maxel BoxInt (Fin 2) (Fin 2) SymForm
gramMaxel2 g u v =
  setMaxelEdge FZ (FS FZ) (metricDot g u v)
    (diagEmbedMaxel (vec2Box (metricQuadrance g u) (metricQuadrance g v)))

||| Exact 2x2 determinant `g00 * g11 - g01^2` of a symmetric `Fin 2` `Maxel`.
public export
detSymMaxel2 : Maxel BoxInt (Fin 2) (Fin 2) SymForm -> BoxInt
detSymMaxel2 m =
  let g00 = lookupMaxel FZ FZ m
      g01 = lookupMaxel FZ (FS FZ) m
      g11 = lookupMaxel (FS FZ) (FS FZ) m
  in g00 * g11 - g01 * g01

||| Planar Euclidean (Blue) metric `diag(+1, +1)` (`Q_b = dx^2 + dy^2`).
public export
blueMetric2 : Maxel BoxInt (Fin 2) (Fin 2) SymForm
blueMetric2 = diagEmbedMaxel (vec2Box 1 1)

||| Planar Minkowski (Red) metric `diag(+1, -1)` (`Q_r = dx^2 - dy^2`).
public export
redMetric2 : Maxel BoxInt (Fin 2) (Fin 2) SymForm
redMetric2 = diagEmbedMaxel (vec2Box 1 (-1))

||| Planar Null (Green) metric `[[0, 1], [1, 0]]` (`Q_g = 2 dx dy`).
public export
greenMetric2 : Maxel BoxInt (Fin 2) (Fin 2) SymForm
greenMetric2 = singletonMaxelEdge {a = Fin 2, b = Fin 2, form = SymForm} FZ (FS FZ) 1

||| 3D Euclidean (Blue) metric `diag(+1, +1, +1)` (`SO(3; Q)` signature).
public export
blueMetric3 : Maxel BoxInt (Fin 3) (Fin 3) SymForm
blueMetric3 = diagEmbedMaxel (vec3Box 1 1 1)

||| (1+2)D Minkowski (Red) metric `diag(+1, -1, -1)` (`SO(1, 2; Q)` signature).
public export
redMetric3 : Maxel BoxInt (Fin 3) (Fin 3) SymForm
redMetric3 = diagEmbedMaxel (vec3Box 1 (-1) (-1))

||| Squaring helper keeping polynomial expressions compact.
public export
sq : Num r => r -> r
sq x = x * x

||| Polarized Archimedes' quadrea polynomial:
||| `A(Q1, Q2, Q3) = 4 Q1 Q2 - (Q1 + Q2 - Q3)^2`.
||| Works identically over integer quadrances (`BoxInt` / `Integer`) and free polynomial rings (`Box BoxInt (Space n)`).
public export
archimedesQuadrea : (Num r, Neg r) => r -> r -> r -> r
archimedesQuadrea q1 q2 q3 =
  let d = q1 + q2 - q3
  in fromInteger 4 * q1 * q2 - d * d

||| Symmetric form of Archimedes' quadrea polynomial: `(Q1 + Q2 + Q3)^2 - 2 (Q1^2 + Q2^2 + Q3^2)`.
public export
archimedesQuadreaSym : (Num r, Neg r) => r -> r -> r -> r
archimedesQuadreaSym q1 q2 q3 =
  let s = q1 + q2 + q3
  in s * s - fromInteger 2 * (sq q1 + sq q2 + sq q3)

--------------------------------------------------------------------------------
-- 4. COMPILE-TIME `QTT 0` UNIVERSAL AFFINE & CHROMOGEOMETRY PROOFS
--------------------------------------------------------------------------------

public export
0 prfAntisymSingleEdge :
  (let p0 : Space 2
       p0 = [0, 0]
       p1 : Space 2
       p1 = [1, 0]
       e  = FinScBox.Box.singletonMaxelEdge {form = AntisymForm} p0 p1 (MkBoxInt 12)
   in (FinScBox.Box.maxelNodeCount e == 1) &&
      (FinScBox.Box.traceMaxel e == MkBoxInt 0) &&
      (FinScBox.Box.lookupMaxel p1 p0 e == MkBoxInt (-12))) = True
prfAntisymSingleEdge = Refl

public export
0 prfPureStepShift :
  FinScSpace.Geometry.Affine.mkPureCoord [-8, 7, -3] + wrapBox (FinScSpace.Geometry.Affine.axisAtom 0)
  = FinScSpace.Geometry.Affine.mkPureCoord [-7, 7, -3]
prfPureStepShift = Refl

public export
0 prfEdgeKeyRoundTrip :
  (let pA = mkPureCoord [-2, 5, 1]
       pB = mkPureCoord [-1, 5, 1]
       k  = mkEdgeKey pA pB
   in case unpackEdgeKey k of
        Just (a, b) => (a == pA) && (b == pB)
        Nothing     => False) = True
prfEdgeKeyRoundTrip = Refl

||| Universal `QTT 0` equivalence of symmetric and polarized Archimedes forms in `Z[q1, q2, q3]`.
public export
0 prfArchimedesSymmetryUniversal :
  (let q1 = polyVar {n = 3} FZ
       q2 = polyVar {n = 3} (FS FZ)
       q3 = polyVar {n = 3} (FS (FS FZ))
   in archimedesQuadreaSym q1 q2 q3 == archimedesQuadrea q1 q2 q3) = True
prfArchimedesSymmetryUniversal = Refl

||| Universal `QTT 0` proof of Wildberger's Triple Quad Formula over all commutative rings:
||| for 3 collinear 1D displacements `d1, d2` (`q1 = d1^2, q2 = d2^2, q3 = (d1 + d2)^2`) in `Z[d1, d2]`,
||| `A(q1, q2, q3) == 0`.
public export
0 prfTripleQuadUniversal :
  (let d1 = polyVar {n = 2} FZ
       d2 = polyVar {n = 2} (FS FZ)
   in archimedesQuadrea (sq d1) (sq d2) (sq (d1 + d2)) == BoxLeaf) = True
prfTripleQuadUniversal = Refl

||| Universal `QTT 0` proof of Wildberger's Chromogeometry Three-Fold Quadrea Theorem
||| in `Z[x1, y1, x2, y2]` for triangle `(0,0), (x1,y1), (x2,y2)`:
||| `A_Blue == -A_Red == -A_Green`.
public export
0 prfThreeFoldQuadreaUniversal :
  (let x1 = polyVar {n = 4} FZ
       y1 = polyVar {n = 4} (FS FZ)
       x2 = polyVar {n = 4} (FS (FS FZ))
       y2 = polyVar {n = 4} (FS (FS (FS FZ)))
       dx = x2 - x1
       dy = y2 - y1
       ab = archimedesQuadrea (sq x2 + sq y2) (sq x1 + sq y1) (sq dx + sq dy)
       ar = archimedesQuadrea (sq x2 - sq y2) (sq x1 - sq y1) (sq dx - sq dy)
       ag = archimedesQuadrea (2 * x2 * y2)   (2 * x1 * y1)   (2 * dx * dy)
   in ((ab + ar) == BoxLeaf) && ((ab + ag) == BoxLeaf)) = True
prfThreeFoldQuadreaUniversal = Refl
