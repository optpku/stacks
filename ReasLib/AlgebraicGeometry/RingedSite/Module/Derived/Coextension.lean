/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coextension
public import ReasLib.CategoryTheory.Adjunction.Derived.Unbounded

@[expose] public section

/-!
# Derived coextension on a ringed site

For a morphism of commutative ring sheaves on a fixed site, this file constructs the
K-injective total right-derived coextension functor and its adjunction with derived restriction
of scalars.
-/

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.DerivedCoextension

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat] [HasSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable {𝒪 𝒪' : Sheaf J CommRingCat.{max u v}}

/-- The standard unbounded derived-category structure for modules over a commutative ring sheaf. -/
noncomputable instance moduleHasDerivedCategory
    (O : Sheaf J CommRingCat.{max u v}) :
    HasDerivedCategory (SheafOfModules (CategoryTheory.Sheaf.ringSheafOfComm O)) :=
  HasDerivedCategory.standard (SheafOfModules (CategoryTheory.Sheaf.ringSheafOfComm O))

/-- Same-site restriction of scalars preserves finite limits. -/
instance restrictionPreservesFiniteLimits (α : 𝒪 ⟶ 𝒪') :
    CategoryTheory.Limits.PreservesFiniteLimits (restrictionAlong α) := sorry

/-- Same-site restriction of scalars preserves finite colimits. -/
instance restrictionPreservesFiniteColimits (α : 𝒪 ⟶ 𝒪') :
    CategoryTheory.Limits.PreservesFiniteColimits (restrictionAlong α) := sorry

/-- Restriction along a morphism of commutative ring sheaves, bundled with its exactness. -/
noncomputable def restrictionExact (α : 𝒪 ⟶ 𝒪') :
    ringedSiteModuleCategory J 𝒪' ⥤ₑ ringedSiteModuleCategory J 𝒪 :=
  ⟨restrictionAlong α, restrictionAlong_exact α⟩

/-- Forgetting the exact structure on `restrictionExact α` recovers restriction along `α`. -/
theorem restrictionExact_obj (α : 𝒪 ⟶ 𝒪') :
    (restrictionExact α).obj = restrictionAlong α := sorry

/-- The functor induced by restriction of scalars on unbounded derived categories. -/
noncomputable abbrev restriction (α : 𝒪 ⟶ 𝒪') :
    DerivedCategory (ringedSiteModuleCategory J 𝒪') ⥤
      DerivedCategory (ringedSiteModuleCategory J 𝒪) :=
  Adjunction.Derived.KInjective.left (restrictionExact α)

/-- Derived restriction agrees with the canonical derived-category action of restriction. -/
theorem restriction_eq_mapDerivedCategory (α : 𝒪 ⟶ 𝒪') :
    restriction α = (restrictionAlong α).mapDerivedCategory := sorry

/-- Same-site coextension is additive because it is right adjoint to additive restriction. -/
noncomputable instance coextendAdditive (α : 𝒪 ⟶ 𝒪') :
    (coextendAlong α).Additive := sorry

/-- The K-injective total right-derived coextension functor. -/
noncomputable abbrev functor (α : 𝒪 ⟶ 𝒪') :
    DerivedCategory (ringedSiteModuleCategory J 𝒪) ⥤
      DerivedCategory (ringedSiteModuleCategory J 𝒪') :=
  Adjunction.Derived.KInjective.right (coextendAlong α)

/-- Derived restriction of scalars is left adjoint to total right-derived coextension. -/
noncomputable def adjunction (α : 𝒪 ⟶ 𝒪') :
    restriction α ⊣ functor α :=
  Adjunction.Derived.KInjective.adjunction (restrictionExact α)
    (coextendAlong α) (restrictionCoextendAdj α)

/-- The Hom equivalence supplied by the derived restriction-coextension adjunction. -/
noncomputable def homEquiv (α : 𝒪 ⟶ 𝒪')
    (K : DerivedCategory (ringedSiteModuleCategory J 𝒪'))
    (M : DerivedCategory (ringedSiteModuleCategory J 𝒪)) :
    ((restriction α).obj K ⟶ M) ≃ (K ⟶ (functor α).obj M) :=
  (adjunction α).homEquiv K M

/-- Total right-derived coextension is canonically a right adjoint. -/
noncomputable instance functorIsRightAdjoint (α : 𝒪 ⟶ 𝒪') :
    (functor α).IsRightAdjoint := sorry

end SheafOfModules.RingedSite.DerivedCoextension
