module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import stacks_project.Chap66.Lemma_66_5_5_PointsTopology
public import stacks_project.Chap66.Lemma_66_12_3
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap71.Lemma_71_6_12_Pullback

/-!
# Étale-local characterizations of effective Cartier divisors

Principal closed subschemes `Spec(A / (f))` of a scheme over `S`, and the
étale-scheme conditions equivalent to a closed subspace being an effective
Cartier divisor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped AlgebraicGeometry nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The scheme `Spec(A / (f))` over `S`, for `U : Over S` with global sections `A`
and `f : Γ(U.left, ⊤)`. -/
def principalSubschemeOver {S : Scheme.{u}} (U : Over S) (f : Γ(U.left, ⊤)) :
    Over S :=
  Over.mk ((Scheme.IdealSheafData.ofIdealTop (Ideal.span {f})).subschemeι ≫ U.hom)

/-- The structure morphism of `principalSubschemeOver U f` is the composite of the
principal closed immersion with `U.hom`. -/
theorem principalSubschemeOver_hom {S : Scheme.{u}} (U : Over S)
    (f : Γ(U.left, ⊤)) :
    (principalSubschemeOver U f).hom =
      (Scheme.IdealSheafData.ofIdealTop (Ideal.span {f})).subschemeι ≫ U.hom :=
  sorry

/-- The closed immersion `Spec(A / (f)) ⟶ U` as a morphism of algebraic spaces
over `S`. -/
def principalι {S : Scheme.{u}} (U : Over S) (f : Γ(U.left, ⊤)) :
    ofOver (principalSubschemeOver U f) ⟶ ofOver U :=
  ofOverMap
    (Over.homMk (Scheme.IdealSheafData.ofIdealTop (Ideal.span {f})).subschemeι rfl)

/-- `principalι U f` is `ofOverMap` of the `Over S` morphism induced by the
principal closed immersion. -/
theorem principalι_spec {S : Scheme.{u}} (U : Over S) (f : Γ(U.left, ⊤)) :
    principalι U f =
      ofOverMap
        (Over.homMk
          (Scheme.IdealSheafData.ofIdealTop (Ideal.span {f})).subschemeι rfl) :=
  sorry

namespace ClosedSubspace

/-- The inverse image `D ×_X U` equals the principal closed subscheme of `f` over
`U`, as an isomorphism in `Over (ofOver U)`. -/
def inverseImage_isPrincipal {S : Scheme.{u}} {X : AlgebraicSpace S}
    (D : ClosedSubspace X) {U : Over S} (φ : ofOver U ⟶ X)
    (f : Γ(U.left, ⊤)) : Prop :=
  Nonempty (Over.mk (D.inverseImage φ).ι ≅ Over.mk (principalι U f))

/-- `inverseImage_isPrincipal D φ f` is the existence of an isomorphism over
`ofOver U` between `D.inverseImage φ` and the principal closed subscheme of
`f`. -/
theorem inverseImage_isPrincipal_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (D : ClosedSubspace X) {U : Over S} (φ : ofOver U ⟶ X)
    (f : Γ(U.left, ⊤)) :
    D.inverseImage_isPrincipal φ f ↔
      Nonempty (Over.mk (D.inverseImage φ).ι ≅ Over.mk (principalι U f)) :=
  sorry

end ClosedSubspace

namespace IsEffectiveCartierDivisor

/-- There is a scheme `U` over `S` and a surjective étale morphism
`φ : ofOver U ⟶ X` whose inverse image of `D` is an effective Cartier
divisor. -/
def existsSurjectiveEtaleScheme {S : Scheme.{u}} {X : AlgebraicSpace S}
    (D : ClosedSubspace X) : Prop :=
  ∃ (U : Over S) (φ : ofOver U ⟶ X),
    Etale φ ∧ Surjective φ ∧ IsEffectiveCartierDivisor (D.inverseImage φ).ι

/-- `existsSurjectiveEtaleScheme D` is the existence of a surjective étale
scheme atlas along which the inverse image of `D` is effective Cartier. -/
theorem existsSurjectiveEtaleScheme_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (D : ClosedSubspace X) :
    existsSurjectiveEtaleScheme D ↔
      ∃ (U : Over S) (φ : ofOver U ⟶ X),
        Etale φ ∧ Surjective φ ∧
          IsEffectiveCartierDivisor (D.inverseImage φ).ι :=
  sorry

namespace existsSurjectiveEtaleScheme

/-- A surjective étale scheme atlas along which the inverse image of `D` is
effective Cartier witnesses `existsSurjectiveEtaleScheme D`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {D : ClosedSubspace X}
    {U : Over S} (φ : ofOver U ⟶ X) [Etale φ] [Surjective φ]
    (h : IsEffectiveCartierDivisor (D.inverseImage φ).ι) :
    existsSurjectiveEtaleScheme D :=
  sorry

/-- `existsSurjectiveEtaleScheme D` supplies a surjective étale scheme atlas
along which the inverse image of `D` is effective Cartier. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} {D : ClosedSubspace X}
    (h : existsSurjectiveEtaleScheme D) :
    ∃ (U : Over S) (φ : ofOver U ⟶ X),
      Etale φ ∧ Surjective φ ∧
        IsEffectiveCartierDivisor (D.inverseImage φ).ι :=
  sorry

end existsSurjectiveEtaleScheme

/-- For every scheme `U` over `S` and every étale morphism `φ : ofOver U ⟶ X`,
the inverse image of `D` is an effective Cartier divisor. -/
def forallEtaleScheme {S : Scheme.{u}} {X : AlgebraicSpace S}
    (D : ClosedSubspace X) : Prop :=
  ∀ (U : Over S) (φ : ofOver U ⟶ X) [Etale φ],
    IsEffectiveCartierDivisor (D.inverseImage φ).ι

/-- `forallEtaleScheme D` is the universal étale-scheme inverse-image condition. -/
theorem forallEtaleScheme_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (D : ClosedSubspace X) :
    forallEtaleScheme D ↔
      ∀ (U : Over S) (φ : ofOver U ⟶ X) [Etale φ],
        IsEffectiveCartierDivisor (D.inverseImage φ).ι :=
  sorry

namespace forallEtaleScheme

/-- The universal étale-scheme inverse-image condition witnesses
`forallEtaleScheme D`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {D : ClosedSubspace X}
    (h : ∀ (U : Over S) (φ : ofOver U ⟶ X) [Etale φ],
      IsEffectiveCartierDivisor (D.inverseImage φ).ι) :
    forallEtaleScheme D :=
  sorry

/-- Under `forallEtaleScheme D`, the inverse image of `D` along any étale
morphism from a scheme is effective Cartier. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} {D : ClosedSubspace X}
    (h : forallEtaleScheme D) :
    ∀ (U : Over S) (φ : ofOver U ⟶ X) [Etale φ],
      IsEffectiveCartierDivisor (D.inverseImage φ).ι :=
  sorry

end forallEtaleScheme

/-- For every point of `|D|` there is an étale morphism from an affine scheme
`(U, u) ⟶ (X, x)` such that `D ×_X U` is `Spec(A / (f))` for a nonzerodivisor
`f`. -/
def existsAffineEtaleNonZeroDivisor {S : Scheme.{u}} {X : AlgebraicSpace S}
    (D : ClosedSubspace X) : Prop :=
  ∀ (x : Points X), x ∈ D.pointsSet →
    ∃ (U : Over S) (φ : ofOver U ⟶ X) (u : U.left) (f : Γ(U.left, ⊤)),
      AlgebraicGeometry.IsAffine U.left ∧ Etale φ ∧
        Points.mapOfOver φ u = x ∧ f ∈ nonZeroDivisors Γ(U.left, ⊤) ∧
          D.inverseImage_isPrincipal φ f

/-- `existsAffineEtaleNonZeroDivisor D` is the pointed affine étale
nonzerodivisor presentation of `D` at every point of `|D|`. -/
theorem existsAffineEtaleNonZeroDivisor_iff {S : Scheme.{u}}
    {X : AlgebraicSpace S} (D : ClosedSubspace X) :
    existsAffineEtaleNonZeroDivisor D ↔
      ∀ (x : Points X), x ∈ D.pointsSet →
        ∃ (U : Over S) (φ : ofOver U ⟶ X) (u : U.left) (f : Γ(U.left, ⊤)),
          AlgebraicGeometry.IsAffine U.left ∧ Etale φ ∧
            Points.mapOfOver φ u = x ∧ f ∈ nonZeroDivisors Γ(U.left, ⊤) ∧
              D.inverseImage_isPrincipal φ f :=
  sorry

/-- Inverse image along an étale morphism from a scheme preserves being an
effective Cartier divisor. -/
instance instInverseImage_etaleScheme {S : Scheme.{u}} {X : AlgebraicSpace S}
    (D : ClosedSubspace X) {U : Over S} (φ : ofOver U ⟶ X)
    [IsEffectiveCartierDivisor D.ι] [Etale φ] :
    IsEffectiveCartierDivisor (D.inverseImage φ).ι :=
  sorry

end IsEffectiveCartierDivisor

end AlgebraicGeometry.AlgebraicSpace
