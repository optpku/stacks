/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Degree.Functor

/-!
# Graded-algebra pullbacks for relative projective spectra

This leaf records concrete degreewise pullback data for graded algebra sheaves.
It is independent of the functorial base-change comparison built from that
data.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {S S' : Scheme.{u}}
variable {𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf}

/-- Sections of the pulled-back degree-`n` piece of a graded algebra sheaf over an open of the
target scheme. -/
abbrev pulledBackGradedAlgebraSection
    (g : S' ⟶ S) (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf)
    (n : ℤ) (U : (S'.Opens)ᵒᵖ) :=
  ((Scheme.Modules.pullback g).obj (𝒜 n)).val.obj U

/-- Concrete data identifying a graded algebra sheaf with the pullback of another graded algebra
sheaf, including chosen pulled-back unit and multiplication operations. -/
structure RelativeProjGradedPullback
    (g : S' ⟶ S) (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf)
    (𝒜' : GradedAlgebraSheaf.{u, u} S'.sheaf) where
  /-- The degreewise identifications with the pullback of `𝒜`. -/
  degreeIso : ∀ n : ℤ, ((Scheme.Modules.pullback g).obj (𝒜 n)) ≅ 𝒜' n
  /-- A chosen degree-zero unit section before transporting along `degreeIso`. -/
  pullbackOne : ∀ U : (S'.Opens)ᵒᵖ, pulledBackGradedAlgebraSection g 𝒜 0 U
  /-- Chosen multiplication on the pulled-back degree pieces before transport along `degreeIso`. -/
  pullbackMul : ∀ (U : (S'.Opens)ᵒᵖ) (n m : ℤ),
    pulledBackGradedAlgebraSection g 𝒜 n U →ₗ[S'.presheaf.obj U]
      pulledBackGradedAlgebraSection g 𝒜 m U →ₗ[S'.presheaf.obj U]
        pulledBackGradedAlgebraSection g 𝒜 (n + m) U
  /-- Transporting the chosen unit along the degree-zero isomorphism gives the unit of `𝒜'`. -/
  map_one : ∀ U : (S'.Opens)ᵒᵖ,
    (((degreeIso 0).hom.val.app U).hom) (pullbackOne U) = 𝒜'.one U
  /-- Transporting the chosen multiplication along the degreewise isomorphisms gives the
  multiplication of `𝒜'`. -/
  map_mul : ∀ (U : (S'.Opens)ᵒᵖ) (n m : ℤ)
    (a : pulledBackGradedAlgebraSection g 𝒜 n U)
    (b : pulledBackGradedAlgebraSection g 𝒜 m U),
    (((degreeIso (n + m)).hom.val.app U).hom) (pullbackMul U n m a b) =
      𝒜'.mul U n m ((((degreeIso n).hom.val.app U).hom) a)
        ((((degreeIso m).hom.val.app U).hom) b)

namespace RelativeProjGradedPullback

/-- Construct graded pullback data from degreewise isomorphisms and chosen
operations whose transports agree with the target graded algebra. -/
def ofDegreeIso
    {g : S' ⟶ S}
    {𝒜' : GradedAlgebraSheaf.{u, u} S'.sheaf}
    (degreeIso : ∀ n : ℤ, ((Scheme.Modules.pullback g).obj (𝒜 n)) ≅ 𝒜' n)
    (pullbackOne : ∀ U : (S'.Opens)ᵒᵖ, pulledBackGradedAlgebraSection g 𝒜 0 U)
    (pullbackMul : ∀ (U : (S'.Opens)ᵒᵖ) (n m : ℤ),
      pulledBackGradedAlgebraSection g 𝒜 n U →ₗ[S'.presheaf.obj U]
        pulledBackGradedAlgebraSection g 𝒜 m U →ₗ[S'.presheaf.obj U]
          pulledBackGradedAlgebraSection g 𝒜 (n + m) U)
    (map_one : ∀ U : (S'.Opens)ᵒᵖ,
      (((degreeIso 0).hom.val.app U).hom) (pullbackOne U) = 𝒜'.one U)
    (map_mul : ∀ (U : (S'.Opens)ᵒᵖ) (n m : ℤ)
      (a : pulledBackGradedAlgebraSection g 𝒜 n U)
      (b : pulledBackGradedAlgebraSection g 𝒜 m U),
      (((degreeIso (n + m)).hom.val.app U).hom) (pullbackMul U n m a b) =
        𝒜'.mul U n m ((((degreeIso n).hom.val.app U).hom) a)
          ((((degreeIso m).hom.val.app U).hom) b)) :
    RelativeProjGradedPullback g 𝒜 𝒜' where
  degreeIso := degreeIso
  pullbackOne := pullbackOne
  pullbackMul := pullbackMul
  map_one := map_one
  map_mul := map_mul

/-- The section map induced by the degree-`n` pullback identification. -/
abbrev degreeMap
    {g : S' ⟶ S}
    {𝒜' : GradedAlgebraSheaf.{u, u} S'.sheaf}
    (pullback : RelativeProjGradedPullback g 𝒜 𝒜')
    (n : ℤ) (U : (S'.Opens)ᵒᵖ) :
    pulledBackGradedAlgebraSection g 𝒜 n U →ₗ[S'.presheaf.obj U] (𝒜' n).val.obj U :=
  ((pullback.degreeIso n).hom.val.app U).hom

/-- The chosen unit and multiplication data transport to the corresponding operations of the
target graded algebra. -/
theorem spec
    {g : S' ⟶ S}
    {𝒜' : GradedAlgebraSheaf.{u, u} S'.sheaf}
    (pullback : RelativeProjGradedPullback g 𝒜 𝒜') :
    (∀ U : (S'.Opens)ᵒᵖ, pullback.degreeMap 0 U (pullback.pullbackOne U) = 𝒜'.one U) ∧
    (∀ (U : (S'.Opens)ᵒᵖ) (n m : ℤ)
      (a : pulledBackGradedAlgebraSection g 𝒜 n U)
      (b : pulledBackGradedAlgebraSection g 𝒜 m U),
      pullback.degreeMap (n + m) U (pullback.pullbackMul U n m a b) =
        𝒜'.mul U n m (pullback.degreeMap n U a) (pullback.degreeMap m U b)) := sorry

end RelativeProjGradedPullback

end AlgebraicGeometry.Scheme
