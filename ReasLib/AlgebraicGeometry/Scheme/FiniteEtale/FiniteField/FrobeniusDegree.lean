module

public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.FiniteEtale.Automorphism
public import ReasLib.Topology.Algebra.Category.ProfiniteGrp.HatZ
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.FieldTheory.Perfect

/-!
# Finite-field coordinates for geometric Frobenius degree

The reverse map to profinite integers evaluates the actual fiber automorphism
on finite-field covers and assembles the finite quotient coordinates.
-/

@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.PreGaloisCategory
noncomputable section
open ProfiniteGrp (integerGroup hatZ)

namespace AlgebraicGeometry.Scheme.FiniteEtale.FiniteField

variable (p : ℕ) [Fact p.Prime]

/-- The prime-field algebra is obtained from the specified spectrum morphism. -/
abbrev pointAlgebra (s : GeometricPoint (Spec (.of (ZMod p)))) : Algebra (ZMod p) s.K :=
  (Spec.preimage s.hom).hom.toAlgebra

/-- The characteristic of the point field follows from its actual scalar map. -/
theorem point_charP (s : GeometricPoint (Spec (.of (ZMod p)))) : CharP s.K p := sorry

/-- Inverse p-power on the actual algebraically closed source field. -/
def geometricRingEquiv (s : GeometricPoint (Spec (.of (ZMod p)))) : s.K ≃+* s.K :=
  letI : IsAlgClosed s.K := s.isAlgClosed
  letI : CharP s.K p := point_charP p s
  (frobeniusEquiv s.K p).symm

/-- The spectrum automorphism induced by inverse p-power. -/
def geometricSpecIso (s : GeometricPoint (Spec (.of (ZMod p)))) :
    Spec (.of s.K) ≅ Spec (.of s.K) :=
  Scheme.Spec.mapIso (geometricRingEquiv p s).toCommRingCatIso.op

theorem geometric_over (s : GeometricPoint (Spec (.of (ZMod p)))) :
    (geometricSpecIso p s).hom ≫ s.hom = s.hom := sorry

/-- Geometric Frobenius acts on the finite fibers by actual precomposition. -/
def geometricFrobenius (s : GeometricPoint (Spec (.of (ZMod p)))) : Aut s.finiteFiber :=
  s.finiteFiberAut (geometricSpecIso p s) (geometric_over p s)

/-- A finite quotient of the actual lifted integer group. -/
abbrev IntegerQuotient (H : FiniteIndexNormalSubgroup integerGroup.{1}) :=
  integerGroup.{1} ⧸ H.toSubgroup

/-- Its finite cardinality specifies the degree of the testing finite field. -/
def quotientDegree (H : FiniteIndexNormalSubgroup integerGroup.{1}) : ℕ :=
  Nat.card (IntegerQuotient H)

theorem quotientDegree_pos (H : FiniteIndexNormalSubgroup integerGroup.{1}) :
    0 < quotientDegree H := sorry

/-- The finite splitting field of the polynomial of the specified quotient degree. -/
abbrev quotientField (H : FiniteIndexNormalSubgroup integerGroup.{1}) :=
  GaloisField p (quotientDegree H)

/-- The actual prime-field spectrum morphism. -/
def quotientFieldMap (H : FiniteIndexNormalSubgroup integerGroup.{1}) :
    Spec (.of (quotientField p H)) ⟶ Spec (.of (ZMod p)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (quotientField p H)))

theorem quotientFieldMap_finite (H : FiniteIndexNormalSubgroup integerGroup.{1}) :
    IsFinite (quotientFieldMap p H) := sorry

theorem quotientFieldMap_etale (H : FiniteIndexNormalSubgroup integerGroup.{1}) :
    Etale (quotientFieldMap p H) := sorry

/-- The test cover has its actual field spectrum and scalar morphism. -/
def quotientCover (H : FiniteIndexNormalSubgroup integerGroup.{1}) :
    Scheme.FiniteEtale (Spec (.of (ZMod p))) :=
  { toComma := Over.mk (quotientFieldMap p H)
    prop := ⟨quotientFieldMap_finite p H, quotientFieldMap_etale p H⟩ }

/-- The test cover retains the finite-field spectrum as its actual scheme. -/
@[simp]
theorem quotientCover_left (H : FiniteIndexNormalSubgroup integerGroup.{1}) :
    (quotientCover p H).left = Spec (.of (quotientField p H)) := rfl

/-- The test cover retains the original prime-field scalar morphism. -/
@[simp]
theorem quotientCover_hom (H : FiniteIndexNormalSubgroup integerGroup.{1}) :
    (quotientCover p H).hom = quotientFieldMap p H := rfl

/-- A native proved algebraic-embedding construction supplies a test fiber point. -/
def quotientEmbedding (s : GeometricPoint (Spec (.of (ZMod p))))
    (H : FiniteIndexNormalSubgroup integerGroup.{1}) :
    letI := pointAlgebra p s
    quotientField p H →ₐ[ZMod p] s.K := by
  letI := pointAlgebra p s
  letI : IsAlgClosed s.K := s.isAlgClosed
  exact IsAlgClosed.lift

/-- The actual spectrum lift underlying the test point. -/
def quotientPointLift (s : GeometricPoint (Spec (.of (ZMod p))))
    (H : FiniteIndexNormalSubgroup integerGroup.{1}) :
    Spec (.of s.K) ⟶ (quotientCover p H).left :=
  letI := pointAlgebra p s
  Spec.map (CommRingCat.ofHom (quotientEmbedding p s H).toRingHom)

theorem quotientPointLift_fac (s : GeometricPoint (Spec (.of (ZMod p))))
    (H : FiniteIndexNormalSubgroup integerGroup.{1}) :
    quotientPointLift p s H ≫ (quotientCover p H).hom = s.hom := sorry

/-- A specified actual fiber point, not selected from a new existence law. -/
def quotientPoint (s : GeometricPoint (Spec (.of (ZMod p))))
    (H : FiniteIndexNormalSubgroup integerGroup.{1}) : s.finiteFiber.obj (quotientCover p H) :=
  Over.homMk (quotientPointLift p s H) (quotientPointLift_fac p s H)

/-- The chosen fiber point has the explicitly embedded spectrum lift. -/
@[simp]
theorem quotientPoint_left (s : GeometricPoint (Spec (.of (ZMod p))))
    (H : FiniteIndexNormalSubgroup integerGroup.{1}) :
    (quotientPoint p s H).left = quotientPointLift p s H := rfl

/-- The class of the integer one generates each finite quotient. -/
def quotientGenerator (H : FiniteIndexNormalSubgroup integerGroup.{1}) : IntegerQuotient H :=
  QuotientGroup.mk (Multiplicative.ofAdd (ULift.up (1 : ℤ)))

/-- A finite evaluation computes the geometric Frobenius exponent in the actual quotient. -/
def degreeCoordinate (s : GeometricPoint (Spec (.of (ZMod p))))
    (H : FiniteIndexNormalSubgroup integerGroup.{1}) (σ : Aut s.finiteFiber) :
    IntegerQuotient H := by
  classical
  exact ∏ j : Fin (quotientDegree H),
    if σ.hom.app (quotientCover p H) (quotientPoint p s H) =
        ((geometricFrobenius p s) ^ j.val).hom.app (quotientCover p H) (quotientPoint p s H)
    then quotientGenerator H ^ j.val
    else 1

/-- The degree-one quotient has its unique identity coordinate. -/
theorem degreeCoordinate_eq_one_of_degree_eq_one
    (s : GeometricPoint (Spec (.of (ZMod p))))
    (H : FiniteIndexNormalSubgroup integerGroup.{1}) (hH : quotientDegree H = 1)
    (σ : Aut s.finiteFiber) : degreeCoordinate p s H σ = 1 := sorry

/-- Naturality makes the finite-field evaluations compatible with quotient maps. -/
theorem degreeCoordinate_naturality (s : GeometricPoint (Spec (.of (ZMod p))))
    {H K : FiniteIndexNormalSubgroup integerGroup.{1}} (f : H ⟶ K) (σ : Aut s.finiteFiber) :
    (ProfiniteGrp.ProfiniteCompletion.diagram integerGroup.{1}).map f (degreeCoordinate p s H σ) =
      degreeCoordinate p s K σ := sorry

/-- The inverse is the actual compatible tuple of finite evaluations. -/
def normalizeDegreeFun (s : GeometricPoint (Spec (.of (ZMod p))))
    (σ : Aut s.finiteFiber) : hatZ.{1} :=
  ⟨fun H ↦ degreeCoordinate p s H σ, fun H K f ↦ degreeCoordinate_naturality p s f σ⟩

/-- The finite coordinate of normalization is its specified finite evaluation. -/
@[simp]
theorem normalizeDegreeFun_apply (s : GeometricPoint (Spec (.of (ZMod p))))
    (σ : Aut s.finiteFiber) (H : FiniteIndexNormalSubgroup integerGroup.{1}) :
    (normalizeDegreeFun p s σ).val H = degreeCoordinate p s H σ := rfl

/-- Signed Frobenius powers have their literal integer class in every quotient. -/
theorem degreeCoordinate_frobenius_zpow (s : GeometricPoint (Spec (.of (ZMod p))))
    (H : FiniteIndexNormalSubgroup integerGroup.{1}) (m : ℤ) :
    degreeCoordinate p s H (geometricFrobenius p s ^ m) =
      QuotientGroup.mk (Multiplicative.ofAdd (ULift.up m)) := sorry

theorem normalizeDegreeFun_one (s : GeometricPoint (Spec (.of (ZMod p)))) :
    normalizeDegreeFun p s 1 = 1 := sorry

theorem normalizeDegreeFun_mul (s : GeometricPoint (Spec (.of (ZMod p))))
    (σ τ : Aut s.finiteFiber) :
    normalizeDegreeFun p s (σ * τ) = normalizeDegreeFun p s σ * normalizeDegreeFun p s τ := sorry

/-- Finite coordinate evaluations are continuous for the native fiber-automorphism topology. -/
theorem normalizeDegreeFun_continuous (s : GeometricPoint (Spec (.of (ZMod p)))) :
    Continuous (normalizeDegreeFun p s) := sorry

/-- The continuous degree map carries the directly constructed quotient coordinates. -/
def normalizeDegree (s : GeometricPoint (Spec (.of (ZMod p)))) :
    ProfiniteGrp.of (Aut s.finiteFiber) ⟶ hatZ.{1} :=
  ProfiniteGrp.ofHom
    { toFun := normalizeDegreeFun p s
      map_one' := normalizeDegreeFun_one p s
      map_mul' := normalizeDegreeFun_mul p s
      continuous_toFun := normalizeDegreeFun_continuous p s }

end AlgebraicGeometry.Scheme.FiniteEtale.FiniteField
