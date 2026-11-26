module FinScSpace.Geometry.Projective

import FinScBox.BoxInt
import FinScBox.Interfaces
import FinScBox.Box
import FinScBox.QuadraticExchange
import FinScSpace.Geometry.Affine

%default total

--------------------------------------------------------------------------------
-- 1. STERLING PROJECTIVE `Proportion` & METRIC-POLYMORPHIC SPREADS
--------------------------------------------------------------------------------

||| Exact division-free projective ratio `[num : den]` in `P^1(Q)`.
||| Invalid degenerate expression `[0 : 0]` fails `isValidProportion` recognition.
public export
record Proportion where
  constructor MkProportion
  propNum : BoxInt
  propDen : BoxInt

||| Sterling recognition predicate excluding `[0 : 0]`.
public export
isValidProportion : Proportion -> Bool
isValidProportion p = not (boxIsZero p.propNum && boxIsZero p.propDen)

||| Recognition predicate for finite affine ratios `[num : den]` (`den /= 0`).
public export
isAffineRatio : Proportion -> Bool
isAffineRatio p = not (boxIsZero p.propDen)

||| Transitive Sterling equality over `P^1(Q)`:
||| valid proportions compare via cross-multiplication; `[0 : 0]` never equates to a valid proportion.
public export
Eq Proportion where
  p1 == p2 =
    case (isValidProportion p1, isValidProportion p2) of
      (True,  True)  => p1.propNum * p2.propDen == p2.propNum * p1.propDen
      (False, False) => True
      _              => False

public export
Show Proportion where
  show p = "(" ++ show p.propNum ++ " : " ++ show p.propDen ++ ")"

||| Rational spread between vectors `u, v` under any `SymForm` metric `g`:
||| `s_g(u, v) = det(Gram_g(u, v)) / (Q_g(u) * Q_g(v))`.
public export
spreadBetween : Ord k => Maxel BoxInt k k SymForm -> Box BoxInt k -> Box BoxInt k -> Proportion
spreadBetween g u v =
  let gm = gramMaxel2 g u v
      qU = lookupMaxel FZ FZ gm
      qV = lookupMaxel (FS FZ) (FS FZ) gm
  in MkProportion (detSymMaxel2 gm) (qU * qV)

||| Three vertex spreads `(s1, s2, s3)` opposite sides `(v2 - v1, v2, v1)` under metric `g`.
public export
triangleSpreads : Ord k => Maxel BoxInt k k SymForm -> (v1, v2 : Box BoxInt k) -> (Proportion, Proportion, Proportion)
triangleSpreads g v1 v2 =
  let v3 = subM v2 v1
  in (spreadBetween g v2 v3, spreadBetween g v1 v3, spreadBetween g v1 v2)

||| Rational cross `c_g(u, v) = (<u, v>_g)^2 / (Q_g(u) * Q_g(v)) = 1 - s_g(u, v)` (`= gamma^2` under `redMetric`).
public export
crossBetween : Ord k => Maxel BoxInt k k SymForm -> Box BoxInt k -> Box BoxInt k -> Proportion
crossBetween g u v =
  let gm  = gramMaxel2 g u v
      g01 = lookupMaxel FZ (FS FZ) gm
      qU  = lookupMaxel FZ FZ gm
      qV  = lookupMaxel (FS FZ) (FS FZ) gm
  in MkProportion (g01 * g01) (qU * qV)

||| Intrinsic spread computed purely from triangle quadrances `(q1, q2, q3)` (coordinate-free).
public export
spreadFromQuadrances : (q1, q2, q3 : BoxInt) -> Proportion
spreadFromQuadrances q1 q2 q3 = MkProportion (archimedesQuadrea q1 q2 q3) (4 * q1 * q2)

||| Intrinsic cross computed purely from triangle quadrances `(q1, q2, q3)` (`(q1 + q2 - q3)^2 / (4 q1 q2)`).
public export
crossFromQuadrances : (q1, q2, q3 : BoxInt) -> Proportion
crossFromQuadrances q1 q2 q3 = MkProportion (sq (q1 + q2 - q3)) (4 * q1 * q2)

||| Triple Spread residual `archimedesQuadrea s1 s2 s3 - 4 s1 s2 s3` (0 on collinear/coplanar triples).
public export
tripleSpreadResidual : (Num r, Neg r) => r -> r -> r -> r
tripleSpreadResidual s1 s2 s3 = archimedesQuadrea s1 s2 s3 - fromInteger 4 * s1 * s2 * s3

||| Exact denominator-cleared test for Wildberger's Triple Spread Law across three affine `Proportion`s.
public export
isTripleSpreadClosed : Proportion -> Proportion -> Proportion -> Bool
isTripleSpreadClosed s1@(MkProportion n1 d1) s2@(MkProportion n2 d2) s3@(MkProportion n3 d3) =
  isAffineRatio s1 && isAffineRatio s2 && isAffineRatio s3 &&
  let a = n1 * d2 * d3
      b = n2 * d1 * d3
      c = n3 * d1 * d2
  in archimedesQuadrea a b c == 4 * n1 * n2 * n3 * d1 * d2 * d3

--------------------------------------------------------------------------------
-- 2. COMPILE-TIME `QTT 0` UNIVERSAL SPREAD LAW, CROSS LAW & TRIPLE SPREAD LAW
--------------------------------------------------------------------------------

||| Universal `QTT 0` proof of the **Spread Law** and **Cross Law** in arbitrary dimension and
||| under ANY symmetric bilinear metric `g` (`Z[g11, g12, g22]`):
|||   `4 * det(Gram_i) == A(Q1, Q2, Q3)` for all three vertices `i in {1, 2, 3}`,
|||   `(s1 / Q1 == s2 / Q2)` cleared of denominators, and
|||   `(Q1 + Q2 - Q3)^2 == 4 * Q1 * Q2 * (1 - s3)`.
public export
0 prfSpreadAndCrossLawUniversal :
  (let g11   = polyVar {n = 3} FZ
       g12   = polyVar {n = 3} (FS FZ)
       g22   = polyVar {n = 3} (FS (FS FZ))
       q1    = g11
       q2    = g22
       q3    = g11 - 2 * g12 + g22
       n3    = q1 * q2 - sq g12
       n2    = q1 * q3 - sq (g12 - g11)
       n1    = q2 * q3 - sq (g22 - g12)
       quadA = archimedesQuadrea q1 q2 q3
       cross = q1 + q2 - q3
   in (4 * n1 == quadA) &&
      (4 * n2 == quadA) &&
      (4 * n3 == quadA) &&
      (sq cross == 4 * (q1 * q2 - n3))) = True
prfSpreadAndCrossLawUniversal = Refl

||| Universal `QTT 0` proof of Wildberger's **Triple Spread Law** in BOTH Blue (Euclidean)
||| and Red (Minkowski Special Relativity / Einstein velocity addition) geometries over `Z[u, v]`:
||| `archimedesQuadrea s2 s3 s1 == 4 s1 s2 s3` cleared of common denominator `(1 + sig u^2)(1 + sig v^2)`.
public export
0 prfTripleSpreadBlueAndRedUniversal :
  (let u  = polyVar {n = 2} FZ
       v  = polyVar {n = 2} (FS FZ)
       aB = sq (v - u)
       bB = sq v * (1 + sq u)
       cB = sq u * (1 + sq v)
       aR = negate (sq (v - u))
       bR = negate (sq v) * (1 - sq u)
       cR = negate (sq u) * (1 - sq v)
   in (archimedesQuadrea bB cB aB == 4 * aB * sq u * sq v) &&
      (archimedesQuadrea bR cR aR == 4 * aR * sq u * sq v)) = True
prfTripleSpreadBlueAndRedUniversal = Refl

--------------------------------------------------------------------------------
-- 3. UNIFIED METRIC-PARAMETERIZED `Rotor` (`SO(3; Q)` & `SO(1, 2; Q)` DIHEDRONS)
--------------------------------------------------------------------------------

||| Unified 4-component rotor `(x, v)` in `P^3(Q)`:
||| - under `blueMetric3` (`diag(+1, +1, +1)`): rational Quaternions / `SO(3; Q)` spatial rotations
||| - under `redMetric3`  (`diag(+1, -1, -1)`): Wildberger Dihedrons / `SO(1, 2; Q)` Lorentz frames
public export
record Rotor where
  constructor MkRotor
  rotorScalar   : BoxInt
  rotorBivector : Box BoxInt (Fin 3)

||| Sterling recognition predicate: canonical bivector tree and non-zero projective point `(0, 0, 0, 0)`.
public export
isValidRotor : Rotor -> Bool
isValidRotor r =
  (case checkBoxBoundsBy (\_ => True) r.rotorBivector of Just _ => True; Nothing => False) &&
  not (boxIsZero r.rotorScalar && r.rotorBivector == BoxLeaf)

public export
Eq Rotor where
  r1 == r2 = r1.rotorScalar == r2.rotorScalar && r1.rotorBivector == r2.rotorBivector

public export
Show Rotor where
  show r = "Rotor(" ++ show r.rotorScalar ++ " : " ++ show r.rotorBivector ++ ")"

||| Projective `P^3(Q)` ray equivalence `(x1 : v1) == (x2 : v2)`.
public export
sameProjectiveRotor : Rotor -> Rotor -> Bool
sameProjectiveRotor r1 r2 =
  isValidRotor r1 && isValidRotor r2 &&
  let a0 = r1.rotorScalar;                  b0 = r2.rotorScalar
      a1 = lookupBox FZ r1.rotorBivector;   b1 = lookupBox FZ r2.rotorBivector
      a2 = lookupBox (FS FZ) r1.rotorBivector; b2 = lookupBox (FS FZ) r2.rotorBivector
      a3 = lookupBox (FS (FS FZ)) r1.rotorBivector; b3 = lookupBox (FS (FS FZ)) r2.rotorBivector
  in (a0 * b1 == a1 * b0) && (a0 * b2 == a2 * b0) && (a0 * b3 == a3 * b0) &&
     (a1 * b2 == a2 * b1) && (a1 * b3 == a3 * b1) && (a2 * b3 == a3 * b2)

public export
idRotor : Rotor
idRotor = MkRotor 1 BoxLeaf

public export
inverseRotor : Rotor -> Rotor
inverseRotor r = MkRotor r.rotorScalar (negateBox r.rotorBivector)

||| Half-stored antisymmetric cross-product `Maxel` `[v]_x` over `Fin 3`.
public export
skewMaxel3 : Box BoxInt (Fin 3) -> Maxel BoxInt (Fin 3) (Fin 3) AntisymForm
skewMaxel3 v =
  let t = lookupBox FZ v
      r = lookupBox (FS FZ) v
      s = lookupBox (FS (FS FZ)) v
  in setMaxelEdge FZ (FS FZ) (negate s)
       (setMaxelEdge FZ (FS (FS FZ)) r
          (singletonMaxelEdge {a = Fin 3, b = Fin 3, form = AntisymForm} (FS FZ) (FS (FS FZ)) (negate t)))

||| Half-stored symmetric 3D Householder mean-reflection `Maxel` (scaled by 3): `2 J_3 - 3 I_3`.
public export
meanReflectionScaled3 : Maxel BoxInt (Fin 3) (Fin 3) SymForm
meanReflectionScaled3 =
  setMaxelEdge FZ (FS FZ) 2
    (setMaxelEdge FZ (FS (FS FZ)) 2
       (setMaxelEdge (FS FZ) (FS (FS FZ)) 2
          (diagEmbedMaxel (vec3Box (-1) (-1) (-1)))))

||| Metric norm `N_g(x, v) = x^2 + Q_g(v)`.
public export
rotorNorm : Maxel BoxInt (Fin 3) (Fin 3) SymForm -> Rotor -> BoxInt
rotorNorm g r = r.rotorScalar * r.rotorScalar + metricQuadrance g r.rotorBivector

public export
skewMaxelG : Maxel BoxInt (Fin 3) (Fin 3) SymForm -> Box BoxInt (Fin 3) -> Maxel BoxInt (Fin 3) (Fin 3) GeneralForm
skewMaxelG g v = composeMaxel (toGeneralMaxel g) (toGeneralMaxel (skewMaxel3 v))

||| Metric-parameterized rotor composition `r2 * r1` (Quaternion product under `blueMetric3`; Dihedron product under `redMetric3`).
public export
composeRotor : Maxel BoxInt (Fin 3) (Fin 3) SymForm -> Rotor -> Rotor -> Rotor
composeRotor g r2 r1 =
  let xOut = (r2.rotorScalar * r1.rotorScalar) - metricDot g r2.rotorBivector r1.rotorBivector
      vOut = scaleM r1.rotorScalar r2.rotorBivector <+>
             scaleM r2.rotorScalar r1.rotorBivector <+>
             actMaxelR (skewMaxelG g r2.rotorBivector) r1.rotorBivector
  in MkRotor xOut vOut

||| Scaled `3x3` orthogonal/Lorentz action `Maxel` preserving `Q_g` up to `(rotorNorm g r)^2`.
public export
rotorActionMaxel : Maxel BoxInt (Fin 3) (Fin 3) SymForm -> Rotor -> Maxel BoxInt (Fin 3) (Fin 3) GeneralForm
rotorActionMaxel g r =
  let gGen = toGeneralMaxel g
      gv   = actMaxelR gGen r.rotorBivector
      base = (r.rotorScalar * r.rotorScalar) - (r.rotorBivector <.> gv)
      id3  = toGeneralMaxel (diagEmbedMaxel (vec3Box base base base))
      symP = MkMaxel (scaleM (MkBoxInt 2) (r.rotorBivector >< gv))
      skwP = scaleM (MkBoxInt 2 * r.rotorScalar) (skewMaxelG g r.rotorBivector)
  in id3 <+> symP <+> skwP

||| Five-way causal classification of a `redMetric3` `(2+1)D` Lorentz `Rotor`.
public export
data CausalLorentzType
  = EllipticSpatialRotation
  | HyperbolicLorentzBoost
  | ParabolicNullRotation
  | InvolutionHalfTurn
  | SingularNullRotor

public export
Eq CausalLorentzType where
  EllipticSpatialRotation == EllipticSpatialRotation = True
  HyperbolicLorentzBoost  == HyperbolicLorentzBoost  = True
  ParabolicNullRotation   == ParabolicNullRotation   = True
  InvolutionHalfTurn      == InvolutionHalfTurn      = True
  SingularNullRotor       == SingularNullRotor       = True
  _                       == _                       = False

public export
Show CausalLorentzType where
  show EllipticSpatialRotation = "EllipticSpatialRotation"
  show HyperbolicLorentzBoost  = "HyperbolicLorentzBoost"
  show ParabolicNullRotation   = "ParabolicNullRotation"
  show InvolutionHalfTurn      = "InvolutionHalfTurn"
  show SingularNullRotor       = "SingularNullRotor"

public export
classifyRedRotor : Rotor -> CausalLorentzType
classifyRedRotor r =
  let n  = rotorNorm redMetric3 r
      qv = metricQuadrance redMetric3 r.rotorBivector
  in if boxIsZero n then SingularNullRotor
     else if boxIsZero r.rotorScalar then InvolutionHalfTurn
     else if qv > 0 then EllipticSpatialRotation
     else if qv < 0 then HyperbolicLorentzBoost
     else ParabolicNullRotation

public export
spatialRotationRotor : (x, t : BoxInt) -> Rotor
spatialRotationRotor x t = MkRotor x (vec3Box t 0 0)

public export
boostRotorAxis1 : (x, u : BoxInt) -> Rotor
boostRotorAxis1 x u = MkRotor x (vec3Box 0 0 (negate u))

public export
boostRotorAxis2 : (x, u : BoxInt) -> Rotor
boostRotorAxis2 x u = MkRotor x (vec3Box 0 u 0)

||| Converts a Pythagorean `QuadraticTriple (a, b, r)` (`a^2 + b^2 = r^2`) into a rational boost `beta = a / r`.
public export
boostFromQuadraticTriple : QuadraticTriple -> Rotor
boostFromQuadraticTriple (MkQuadraticTriple a b r) = boostRotorAxis1 (MkBoxInt (r + b)) (MkBoxInt a)

public export
parabolicNullRotor : (x, s : BoxInt) -> Rotor
parabolicNullRotor x s = MkRotor x (vec3Box s 0 s)

--------------------------------------------------------------------------------
-- 4. 2x2 DIHEDRON `Maxel`, `D (x) D` QUATERNION `AntisymForm`, & `QTT 0` PROOFS
--------------------------------------------------------------------------------

public export
detMaxel2 : Maxel BoxInt (Fin 2) (Fin 2) GeneralForm -> BoxInt
detMaxel2 m =
  lookupMaxel FZ FZ m * lookupMaxel (FS FZ) (FS FZ) m -
  lookupMaxel FZ (FS FZ) m * lookupMaxel (FS FZ) FZ m

||| Canonical isomorphism from a `Rotor` `(x, (t, r, s))` to `2x2` split-quaternion `Maxel` `[[x+s, r-t], [r+t, x-s]]`.
public export
rotorToDihedronMaxel2 : Rotor -> Maxel BoxInt (Fin 2) (Fin 2) GeneralForm
rotorToDihedronMaxel2 (MkRotor x v) =
  let t = lookupBox FZ v
      r = lookupBox (FS FZ) v
      s = lookupBox (FS (FS FZ)) v
  in setMaxelEdge FZ FZ (x + s)
       (setMaxelEdge FZ (FS FZ) (r - t)
          (setMaxelEdge (FS FZ) FZ (r + t)
             (singletonMaxelEdge (FS FZ) (FS FZ) (x - s))))

||| Parabolic nilpotent generator `epsilon = j - i` (`epsilon^2 == emptyMaxel`).
public export
epsilonDihedronMaxel2 : Maxel BoxInt (Fin 2) (Fin 2) GeneralForm
epsilonDihedronMaxel2 = rotorToDihedronMaxel2 (MkRotor 0 (vec3Box (-1) 1 0))

||| Kronecker product of two `2x2` `GeneralForm` `Maxel`s over `(Fin 2, Fin 2)`.
public export
kroneckerMaxel2 :
  Maxel BoxInt (Fin 2) (Fin 2) GeneralForm ->
  Maxel BoxInt (Fin 2) (Fin 2) GeneralForm ->
  Maxel BoxInt (Fin 2, Fin 2) (Fin 2, Fin 2) GeneralForm
kroneckerMaxel2 (MkMaxel m1) (MkMaxel m2) =
  MkMaxel $ foldBox (\(i1, j1), w1, acc1 =>
                      foldBox (\(i2, j2), w2, acc2 =>
                                addAtKeyBox ((i1, i2), (j1, j2)) (w1 * w2) acc2)
                              acc1 m2)
                    BoxLeaf m1

||| Extracts the strict upper triangle (`x < y`) of a `GeneralForm` `Maxel` as canonical `AntisymForm`.
public export
toAntisymMaxel : Ord k => Maxel BoxInt k k GeneralForm -> Maxel BoxInt k k AntisymForm
toAntisymMaxel = foldStoredMaxel (\x, y, w, acc => if x < y then addAtMaxelEdge x y w acc else acc) emptyMaxel

unitMatI2, unitMatJ, unitMatR, unitMatS : Maxel BoxInt (Fin 2) (Fin 2) GeneralForm
unitMatI2 = rotorToDihedronMaxel2 idRotor
unitMatJ  = rotorToDihedronMaxel2 (MkRotor 0 (vec3Box 1 0 0))
unitMatR  = rotorToDihedronMaxel2 (MkRotor 0 (vec3Box 0 1 0))
unitMatS  = rotorToDihedronMaxel2 (MkRotor 0 (vec3Box 0 0 1))

||| Quaternion units `{i, j, k}` embedded inside coupled Dihedron pair `D (x) D` as half-stored `AntisymForm` `Maxel`s.
public export
quatUnitI, quatUnitJ, quatUnitK : Maxel BoxInt (Fin 2, Fin 2) (Fin 2, Fin 2) AntisymForm
quatUnitI = toAntisymMaxel (kroneckerMaxel2 (negM unitMatJ) unitMatS)
quatUnitJ = toAntisymMaxel (kroneckerMaxel2 unitMatI2 unitMatJ)
quatUnitK = toAntisymMaxel (kroneckerMaxel2 unitMatJ unitMatR)

public export
0 prfBlueRotorQuadranceAndReflection :
  (let r1 = MkRotor 1 (vec3Box 1 0 0)
       m1 = rotorActionMaxel blueMetric3 r1
       v0 = vec3Box 3 (-2) 5
       w0 = actMaxelR m1 v0
       n1 = rotorNorm blueMetric3 r1
   in (metricQuadrance blueMetric3 w0 == n1 * n1 * metricQuadrance blueMetric3 v0) &&
      isSymMaxel FinScSpace.Geometry.Projective.meanReflectionScaled3 &&
      (actMaxelR (toGeneralMaxel FinScSpace.Geometry.Projective.meanReflectionScaled3)
                 (actMaxelR (toGeneralMaxel FinScSpace.Geometry.Projective.meanReflectionScaled3) v0)
       == scaleM (MkBoxInt 9) v0)) = True
prfBlueRotorQuadranceAndReflection = Refl

public export
0 prfRedBoostFromPythTriple :
  (let b345 = boostFromQuadraticTriple (MkQuadraticTriple 3 4 5)
       mB   = rotorActionMaxel redMetric3 b345
       wB   = actMaxelR mB (vec3Box 1 0 0)
   in (wB == vec3Box 90 54 0) &&
      (MkProportion (lookupBox (FS FZ) wB) (lookupBox FZ wB) == MkProportion 3 5)) = True
prfRedBoostFromPythTriple = Refl

public export
0 prfDihedronMaxel2IsoAndNilpotent :
  (let r1  = boostRotorAxis2 2 1
       r2  = boostRotorAxis1 3 1
       r12 = composeRotor redMetric3 r2 r1
       d1  = rotorToDihedronMaxel2 r1
       d2  = rotorToDihedronMaxel2 r2
       d12 = rotorToDihedronMaxel2 r12
   in (composeMaxel d2 d1 == d12) &&
      (detMaxel2 d1 == rotorNorm redMetric3 r1) &&
      (detMaxel2 d12 == detMaxel2 d1 * detMaxel2 d2) &&
      (composeMaxel FinScSpace.Geometry.Projective.epsilonDihedronMaxel2
                    FinScSpace.Geometry.Projective.epsilonDihedronMaxel2 == emptyMaxel)) = True
prfDihedronMaxel2IsoAndNilpotent = Refl

public export
0 prfWignerThomasPrecession :
  (let p12 = composeRotor redMetric3 (boostRotorAxis1 3 1) (boostRotorAxis2 2 1)
       p21 = composeRotor redMetric3 (boostRotorAxis2 2 1) (boostRotorAxis1 3 1)
       t12 = lookupBox (the (Fin 3) FZ) p12.rotorBivector
       t21 = lookupBox (the (Fin 3) FZ) p21.rotorBivector
   in (t12 /= 0) && (t12 == negate t21)) = True
prfWignerThomasPrecession = Refl

vec4MatDiagBox : BoxInt -> Box BoxInt (Fin 2, Fin 2)
vec4MatDiagBox c =
  setBox (FZ, FZ) c $ setBox (FZ, FS FZ) c $ setBox (FS FZ, FZ) c $ singletonBox (FS FZ, FS FZ) c

public export
0 prfQuaternionFromDihedronTensor :
  (let gi   = toGeneralMaxel FinScSpace.Geometry.Projective.quatUnitI
       gj   = toGeneralMaxel FinScSpace.Geometry.Projective.quatUnitJ
       gk   = toGeneralMaxel FinScSpace.Geometry.Projective.quatUnitK
       negI = toGeneralMaxel (diagEmbedMaxel (vec4MatDiagBox (-1)))
   in isCanonicalMaxel FinScSpace.Geometry.Projective.quatUnitI &&
      (maxelNodeCount FinScSpace.Geometry.Projective.quatUnitI == 2) &&
      (composeMaxel gi gi == negI) &&
      (composeMaxel gj gj == negI) &&
      (composeMaxel gk gk == negI) &&
      (composeMaxel gi gj == gk)) = True
prfQuaternionFromDihedronTensor = Refl
