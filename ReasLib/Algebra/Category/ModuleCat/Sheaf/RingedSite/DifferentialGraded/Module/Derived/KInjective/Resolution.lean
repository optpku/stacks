/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Derived.KInjective
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.KInjective.Resolution

/-!
# K-injective resolutions in the DG derived category

An objectwise K-injective resolution supplies the canonical derived isomorphism and the function
which computes derived morphisms from homotopy classes into its replacement object.
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
-- sheaf/free elaboration.  Resolution maps are interpreted in the pinned derived structure.
attribute [local instance] Abelian.hasFiniteBiproducts

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedModule.DerivedCategory.KInjective

section


variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

namespace Resolution

/-- The comparison of an objectwise K-injective resolution becomes a canonical isomorphism in
the derived category. -/
noncomputable def iso {𝒜 : DGA(𝒪)} {M : Mod(𝒜, d)}
    (P : Module.KInjective.Resolution M) :
    (Q 𝒜).obj M ≅ (Q 𝒜).obj P.obj :=
  CategoryTheory.Localization.isoOfHom (Q 𝒜)
    (Module.quasiIso 𝒜) P.ι P.quasiIso_ι

/-- The map from homotopy classes into the replacement object to derived morphisms into the
resolved object. -/
noncomputable def homToDerived {𝒜 : DGA(𝒪)} {N : Mod(𝒜, d)}
    (P : Module.KInjective.Resolution N) (M : Mod(𝒜, d)) :
    ((toK 𝒜).obj M ⟶ (toK 𝒜).obj P.obj) →
      ((Q 𝒜).obj M ⟶ (Q 𝒜).obj N) :=
  homToDerivedRep 𝒜 P.ι P.quasiIso_ι

/-- An objectwise K-injective resolution computes derived morphisms from every represented DG
module. -/
theorem homToDerived_bijective {𝒜 : DGA(𝒪)} {N : Mod(𝒜, d)}
    (P : Module.KInjective.Resolution N) (M : Mod(𝒜, d)) :
    Function.Bijective (homToDerived P M) := sorry

end Resolution

namespace ResolutionFunctor

/-- The canonical derived isomorphism attached to a value of a functorial K-injective
resolution. -/
noncomputable def iso {𝒜 : DGA(𝒪)}
    (R : Module.KInjective.ResolutionFunctor 𝒜) (M : Mod(𝒜, d)) :
    (Q 𝒜).obj M ≅ (Q 𝒜).obj (R.toFunctor.obj M) :=
  Resolution.iso (R.resolution M)

/-- A functorial K-injective resolution computes derived morphisms objectwise. -/
theorem homToDerived_bijective {𝒜 : DGA(𝒪)}
    (R : Module.KInjective.ResolutionFunctor 𝒜)
    (M N : Mod(𝒜, d)) :
    Function.Bijective (Resolution.homToDerived (R.resolution N) M) := sorry

end ResolutionFunctor

end


end SheafOfModules.RingedSite.DifferentialGradedModule.DerivedCategory.KInjective
