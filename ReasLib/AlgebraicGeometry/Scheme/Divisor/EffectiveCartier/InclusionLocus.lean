module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.Sober
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheaf.Inclusion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Curve

variable {k : Type u} [Field k] (X T : SchemeOverField k)

/-- A closed subscheme of `X ×_k T` avoids every generic point of every fibre over `T`. -/
def avoidsGenericPointOnFibers (D : (pullback X.hom T.hom).IdealSheafData) : Prop :=
  ∀ t : T.left, ∀ η ∈ genericPoints ((pullback.snd X.hom T.hom).fiber t),
    η ∉ (D.comap ((pullback.snd X.hom T.hom).fiberι t)).support

/-- For a fibrewise non-dense effective Cartier divisor on a smooth projective curve family,
the inclusion ideal is the least base ideal whose pullback makes the first closed subscheme
contained in the second. -/
theorem inclusionIdeal_le_iff
    [IsAlgClosed k] [Curve X] [Smooth X.hom] [Scheme.Hom.FiniteType T.hom]
    (h_projective : ∃ n : ℕ, ∃ i : X.left ⟶ ProjectiveSpace.scheme k n,
      IsClosedImmersion i ∧ i ≫ ProjectiveSpace.toSpec k n = X.hom)
    (D₁ D₂ : (pullback X.hom T.hom).IdealSheafData)
    [IsEffectiveCartierDivisor D₁.subschemeι]
    (hD₁ : avoidsGenericPointOnFibers X T D₁) :
    ∀ J : T.left.IdealSheafData,
      D₁.inclusionIdeal D₂ (pullback.snd X.hom T.hom) ≤ J ↔
        D₂ ≤ D₁ ⊔ J.comap (pullback.snd X.hom T.hom) := sorry

/-- A closed point of a finite-type base lies in the canonical inclusion locus of two
fibrewise non-dense effective Cartier divisors on a smooth projective curve family exactly
when the first scheme-theoretic fibre is contained in the second. -/
theorem mem_inclusionIdeal_support_iff
    [IsAlgClosed k] [Curve X] [Smooth X.hom] [Scheme.Hom.FiniteType T.hom]
    (h_projective : ∃ n : ℕ, ∃ i : X.left ⟶ ProjectiveSpace.scheme k n,
      IsClosedImmersion i ∧ i ≫ ProjectiveSpace.toSpec k n = X.hom)
    (D₁ D₂ : (pullback X.hom T.hom).IdealSheafData)
    [IsEffectiveCartierDivisor D₁.subschemeι]
    [IsEffectiveCartierDivisor D₂.subschemeι]
    (hD₁ : avoidsGenericPointOnFibers X T D₁)
    (hD₂ : avoidsGenericPointOnFibers X T D₂)
    (t : T.left) (ht : t ∈ closedPoints T.left) :
    t ∈ (D₁.inclusionIdeal D₂ (pullback.snd X.hom T.hom)).support ↔
      D₂.comap ((pullback.snd X.hom T.hom).fiberι t) ≤
        D₁.comap ((pullback.snd X.hom T.hom).fiberι t) := sorry

end AlgebraicGeometry.Curve
