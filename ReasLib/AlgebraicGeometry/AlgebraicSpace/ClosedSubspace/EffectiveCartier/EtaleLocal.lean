module

public import Mathlib.Data.List.TFAE
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Closed.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective

/-!
# Étale-local characterizations of effective Cartier divisors

Principal closed subschemes and pointed affine étale presentations characterize
when a closed subspace of an algebraic space is an effective Cartier divisor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped AlgebraicGeometry nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The principal closed subscheme cut out by a global section `f` of `U`, viewed
over `S`. When `U` is affine with coordinate ring `A`, this is `Spec(A / (f))`. -/
def principalSubschemeOver {S : Scheme.{u}} (U : Over S) (f : Γ(U.left, ⊤)) :
    Over S :=
  Over.mk ((Scheme.IdealSheafData.ofIdealTop (Ideal.span {f})).subschemeι ≫ U.hom)

/-- The structure morphism of `principalSubschemeOver U f` is the composite of the
principal closed immersion with `U.hom`. -/
theorem principalSubschemeOver_hom {S : Scheme.{u}} (U : Over S)
    (f : Γ(U.left, ⊤)) :
    (principalSubschemeOver U f).hom =
      (Scheme.IdealSheafData.ofIdealTop (Ideal.span {f})).subschemeι ≫ U.hom :=
  rfl

/-- The inclusion of the principal closed subscheme cut out by `f` into `U`,
viewed as a morphism of algebraic spaces over `S`. For affine `U = Spec(A)`,
its domain is `Spec(A / (f))`. -/
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
  rfl

namespace ClosedSubspace

/-- The inverse image `D ×_X U` equals the principal closed subscheme of `f` over
`U`, as an isomorphism in `Over (ofOver U)`. -/
def inverseImage_isPrincipal {S : Scheme.{u}} {X : AlgebraicSpace S}
    (D : ClosedSubspace X) {U : Over S} (φ : ofOver U ⟶ X)
    (f : Γ(U.left, ⊤)) : Prop :=
  Nonempty (Over.mk (D.inverseImageSubspace φ).ι ≅ Over.mk (principalι U f))

/-- `inverseImage_isPrincipal D φ f` is the existence of an isomorphism over
`ofOver U` between `D.inverseImageSubspace φ` and the principal closed subscheme of
`f`. -/
theorem inverseImage_isPrincipal_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (D : ClosedSubspace X) {U : Over S} (φ : ofOver U ⟶ X)
    (f : Γ(U.left, ⊤)) :
    D.inverseImage_isPrincipal φ f ↔
      Nonempty (Over.mk (D.inverseImageSubspace φ).ι ≅ Over.mk (principalι U f)) :=
  Iff.rfl

end ClosedSubspace

namespace IsEffectiveCartierDivisor

/-- There is a scheme `U` over `S` and a surjective étale morphism
`φ : ofOver U ⟶ X` whose inverse image of `D` is an effective Cartier
divisor. -/
def existsSurjectiveEtaleScheme {S : Scheme.{u}} {X : AlgebraicSpace S}
    (D : ClosedSubspace X) : Prop :=
  ∃ (U : Over S) (φ : ofOver U ⟶ X),
    Etale φ ∧ Surjective φ ∧ IsEffectiveCartierDivisor (D.inverseImageSubspace φ).ι

/-- `existsSurjectiveEtaleScheme D` is the existence of a surjective étale
scheme atlas along which the inverse image of `D` is effective Cartier. -/
theorem existsSurjectiveEtaleScheme_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (D : ClosedSubspace X) :
    existsSurjectiveEtaleScheme D ↔
      ∃ (U : Over S) (φ : ofOver U ⟶ X),
        Etale φ ∧ Surjective φ ∧
          IsEffectiveCartierDivisor (D.inverseImageSubspace φ).ι :=
  Iff.rfl

namespace existsSurjectiveEtaleScheme

/-- A surjective étale scheme atlas along which the inverse image of `D` is
effective Cartier witnesses `existsSurjectiveEtaleScheme D`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {D : ClosedSubspace X}
    {U : Over S} (φ : ofOver U ⟶ X) [Etale φ] [Surjective φ]
    (h : IsEffectiveCartierDivisor (D.inverseImageSubspace φ).ι) :
    existsSurjectiveEtaleScheme D :=
  ⟨U, φ, inferInstance, inferInstance, h⟩

/-- `existsSurjectiveEtaleScheme D` supplies a surjective étale scheme atlas
along which the inverse image of `D` is effective Cartier. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} {D : ClosedSubspace X}
    (h : existsSurjectiveEtaleScheme D) :
    ∃ (U : Over S) (φ : ofOver U ⟶ X),
      Etale φ ∧ Surjective φ ∧
        IsEffectiveCartierDivisor (D.inverseImageSubspace φ).ι :=
  h

end existsSurjectiveEtaleScheme

/-- For every scheme `U` over `S` and every étale morphism `φ : ofOver U ⟶ X`,
the inverse image of `D` is an effective Cartier divisor. -/
def forallEtaleScheme {S : Scheme.{u}} {X : AlgebraicSpace S}
    (D : ClosedSubspace X) : Prop :=
  ∀ (U : Over S) (φ : ofOver U ⟶ X) [Etale φ],
    IsEffectiveCartierDivisor (D.inverseImageSubspace φ).ι

/-- `forallEtaleScheme D` is the universal étale-scheme inverse-image condition. -/
theorem forallEtaleScheme_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (D : ClosedSubspace X) :
    forallEtaleScheme D ↔
      ∀ (U : Over S) (φ : ofOver U ⟶ X) [Etale φ],
        IsEffectiveCartierDivisor (D.inverseImageSubspace φ).ι :=
  Iff.rfl

namespace forallEtaleScheme

/-- The universal étale-scheme inverse-image condition witnesses
`forallEtaleScheme D`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {D : ClosedSubspace X}
    (h : ∀ (U : Over S) (φ : ofOver U ⟶ X) [Etale φ],
      IsEffectiveCartierDivisor (D.inverseImageSubspace φ).ι) :
    forallEtaleScheme D :=
  h

/-- Under `forallEtaleScheme D`, the inverse image of `D` along any étale
morphism from a scheme is effective Cartier. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} {D : ClosedSubspace X}
    (h : forallEtaleScheme D) :
    ∀ (U : Over S) (φ : ofOver U ⟶ X) [Etale φ],
      IsEffectiveCartierDivisor (D.inverseImageSubspace φ).ι :=
  h

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
  Iff.rfl

/-- A closed subspace is an effective Cartier divisor if and only if it is so
after some surjective étale scheme atlas, after every étale scheme chart, or
if it has a principal nonzerodivisor presentation on a pointed affine étale
chart at every point of its support. -/
@[stacks 083C]
theorem tfae {S : Scheme.{u}} {X : AlgebraicSpace S} (D : ClosedSubspace X) :
    List.TFAE
      [IsEffectiveCartierDivisor D.ι, existsSurjectiveEtaleScheme D,
        forallEtaleScheme D, existsAffineEtaleNonZeroDivisor D] :=
  sorry

/-- A closed subspace is an effective Cartier divisor iff some surjective étale
morphism from a scheme pulls it back to an effective Cartier divisor. -/
theorem iff_existsSurjectiveEtaleScheme {S : Scheme.{u}} {X : AlgebraicSpace S}
    (D : ClosedSubspace X) :
    IsEffectiveCartierDivisor D.ι ↔ existsSurjectiveEtaleScheme D :=
  (tfae D).out 0 1

/-- A closed subspace is an effective Cartier divisor iff every étale morphism
from a scheme pulls it back to an effective Cartier divisor. -/
theorem iff_forallEtaleScheme {S : Scheme.{u}} {X : AlgebraicSpace S}
    (D : ClosedSubspace X) :
    IsEffectiveCartierDivisor D.ι ↔ forallEtaleScheme D :=
  (tfae D).out 0 2

/-- A closed subspace is an effective Cartier divisor iff at every point of
`|D|` it is cut out on an affine étale chart by a nonzerodivisor. -/
theorem iff_existsAffineEtaleNonZeroDivisor {S : Scheme.{u}}
    {X : AlgebraicSpace S} (D : ClosedSubspace X) :
    IsEffectiveCartierDivisor D.ι ↔ existsAffineEtaleNonZeroDivisor D :=
  (tfae D).out 0 3

end IsEffectiveCartierDivisor

end AlgebraicGeometry.AlgebraicSpace
