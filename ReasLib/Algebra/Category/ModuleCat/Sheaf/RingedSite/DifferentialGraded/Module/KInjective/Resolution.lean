module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.KInjective.Basic

/-!
# Functorial K-injective resolutions of differential graded modules

The data owner records a functorial replacement, its comparison map, and exactly the two
properties needed by downstream derived-functor constructions.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open DifferentialGradedCategory
open scoped DifferentialGradedCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

-- Mathlib intentionally keeps this construction non-global because a global instance breaks
-- sheaf/free elaboration.  The resolution owner must agree with the imported K-injective choice.
attribute [local instance] Abelian.hasFiniteBiproducts

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedModule.Module

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

namespace KInjective

/-- A K-injective resolution of one DG module consists of its replacement object, comparison
map, quasi-isomorphism property, and combined injectivity instance. -/
structure Resolution {𝒜 : DGA(𝒪)} (M : Mod(𝒜, d)) where
  /-- The K-injective replacement object. -/
  obj : Mod(𝒜, d)
  /-- The comparison from the original DG module. -/
  ι : M ⟶ obj
  /-- The comparison is a quasi-isomorphism. -/
  quasiIso_ι : quasiIso 𝒜 ι
  /-- The replacement is K-injective and graded injective. -/
  [injectiveObj : IsKInjective.GradedInjective obj]

/-- A functorial K-injective resolution consists of a DG-module endofunctor, a comparison from
the identity, and the quasi-isomorphism and injectivity specifications of every value. -/
@[stacks 0FT0]
structure ResolutionFunctor (𝒜 : DGA(𝒪)) where
  /-- The functor assigning a K-injective replacement. -/
  toFunctor : Mod(𝒜, d) ⥤ Mod(𝒜, d)
  /-- The natural quasi-isomorphism into the replacement. -/
  ι : 𝟭 (Mod(𝒜, d)) ⟶ toFunctor
  /-- Every comparison component is a quasi-isomorphism. -/
  quasiIso_ι_app (M : Mod(𝒜, d)) : quasiIso 𝒜 (ι.app M)
  /-- Every replacement is K-injective and graded injective. -/
  [injectiveObj (M : Mod(𝒜, d)) :
    IsKInjective.GradedInjective (toFunctor.obj M)]

namespace ResolutionFunctor

/-- Evaluation of a functorial K-injective resolution gives an objectwise resolution. -/
def resolution {𝒜 : DGA(𝒪)} (R : ResolutionFunctor 𝒜)
    (M : Mod(𝒜, d)) : Resolution M where
  obj := R.toFunctor.obj M
  ι := R.ι.app M
  quasiIso_ι := R.quasiIso_ι_app M
  injectiveObj := R.injectiveObj M

/-- The object of the evaluated resolution is the value of the resolution functor. -/
theorem resolution_obj {𝒜 : DGA(𝒪)} (R : ResolutionFunctor 𝒜)
    (M : Mod(𝒜, d)) :
    (R.resolution M).obj = R.toFunctor.obj M := sorry

/-- The comparison of the evaluated resolution is the corresponding natural-transformation
component. -/
theorem resolution_ι {𝒜 : DGA(𝒪)} (R : ResolutionFunctor 𝒜)
    (M : Mod(𝒜, d)) :
    (R.resolution M).ι = R.ι.app M := sorry

/-- A functorial resolution maps a DG-module morphism between the replacement objects. -/
def map {𝒜 : DGA(𝒪)} (R : ResolutionFunctor 𝒜)
    {M N : Mod(𝒜, d)} (f : M ⟶ N) :
    (R.resolution M).obj ⟶ (R.resolution N).obj :=
  R.toFunctor.map f

/-- Resolution comparison maps are natural in the resolved DG module. -/
theorem ι_naturality {𝒜 : DGA(𝒪)} (R : ResolutionFunctor 𝒜)
    {M N : Mod(𝒜, d)} (f : M ⟶ N) :
    f ≫ (R.resolution N).ι = (R.resolution M).ι ≫ R.map f := sorry

/-- The objectwise resolution map preserves identities. -/
theorem map_id {𝒜 : DGA(𝒪)} (R : ResolutionFunctor 𝒜)
    (M : Mod(𝒜, d)) :
    R.map (𝟙 M) = 𝟙 (R.resolution M).obj := sorry

/-- The objectwise resolution map preserves composition. -/
theorem map_comp {𝒜 : DGA(𝒪)} (R : ResolutionFunctor 𝒜)
    {M N P : Mod(𝒜, d)} (f : M ⟶ N) (g : N ⟶ P) :
    R.map (f ≫ g) = R.map f ≫ R.map g := sorry

/-- Functorial graded-injective K-injective resolutions exist for DG module sheaves. -/
@[stacks 0FT0 "existence"]
theorem nonempty (𝒜 : DGA(𝒪)) :
    Nonempty (ResolutionFunctor 𝒜) := sorry

end ResolutionFunctor

end KInjective

end

end SheafOfModules.RingedSite.DifferentialGradedModule.Module
