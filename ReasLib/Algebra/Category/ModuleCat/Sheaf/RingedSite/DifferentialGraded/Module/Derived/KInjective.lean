/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Derived.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.KInjective.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Morphisms to K-injective objects in the DG derived category

Localization is fully faithful on targets right orthogonal to acyclic DG modules.  Consequently,
morphisms into a K-injective target can be computed in the intrinsic DG homotopy category, and a
quasi-isomorphic K-injective replacement computes derived morphisms.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open DifferentialGradedCategory
open scoped DifferentialGradedCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

-- Mathlib keeps this canonical finite-biproduct construction non-global.  The localization and
-- K-injective orthogonality structures below must share the imported homotopy-category choice.
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

/-- The localization map on morphisms into a K-injective DG homotopy object is bijective. -/
theorem qhMap_bijective (𝒜 : DGA(𝒪))
    (M I : K ℤ Mod(𝒜, d)) (hI : Homotopy.kInjective 𝒜 I) :
    Function.Bijective
      ((Qh 𝒜).map : (M ⟶ I) → ((Qh 𝒜).obj M ⟶ (Qh 𝒜).obj I)) := sorry

/-- A quasi-isomorphism to a K-injective target identifies homotopy morphisms into that target
with derived morphisms into the source of the quasi-isomorphism. -/
noncomputable def homToDerived (𝒜 : DGA(𝒪))
    {M N I : K ℤ Mod(𝒜, d)} (i : N ⟶ I)
    (hi : Homotopy.quasiIso 𝒜 i) :
    (M ⟶ I) → ((Qh 𝒜).obj M ⟶ (Qh 𝒜).obj N) :=
  fun f ↦
    (Qh 𝒜).map f ≫
      (CategoryTheory.Localization.isoOfHom (Qh 𝒜)
        (Homotopy.quasiIso 𝒜) i hi).inv

/-- The map from homotopy morphisms to derived morphisms is localization followed by the
inverse of the localized replacement map. -/
theorem homToDerived_apply (𝒜 : DGA(𝒪))
    {M N I : K ℤ Mod(𝒜, d)} (i : N ⟶ I)
    (hi : Homotopy.quasiIso 𝒜 i) (f : M ⟶ I) :
    homToDerived 𝒜 i hi f =
      (Qh 𝒜).map f ≫
        (CategoryTheory.Localization.isoOfHom (Qh 𝒜)
          (Homotopy.quasiIso 𝒜) i hi).inv := sorry

/-- The map from homotopy morphisms to derived morphisms is natural in its source. -/
theorem homToDerived_naturality_left (𝒜 : DGA(𝒪))
    {M M' N I : K ℤ Mod(𝒜, d)} (i : N ⟶ I)
    (hi : Homotopy.quasiIso 𝒜 i) (g : M' ⟶ M) (f : M ⟶ I) :
    homToDerived 𝒜 i hi (g ≫ f) =
      (Qh 𝒜).map g ≫ homToDerived 𝒜 i hi f := sorry

/-- A quasi-isomorphism to a K-injective target identifies homotopy morphisms into that target
with derived morphisms into the source of the quasi-isomorphism. -/
theorem homToDerived_bijective (𝒜 : DGA(𝒪))
    {M N I : K ℤ Mod(𝒜, d)} (i : N ⟶ I)
    (hi : Homotopy.quasiIso 𝒜 i) (hI : Homotopy.kInjective 𝒜 I) :
    Function.Bijective (homToDerived 𝒜 i hi :
      (M ⟶ I) → ((Qh 𝒜).obj M ⟶ (Qh 𝒜).obj N)) := sorry

/-- The map from represented homotopy classes to derived morphisms computed by a module-level
quasi-isomorphic replacement. -/
noncomputable def homToDerivedRep (𝒜 : DGA(𝒪))
    {M N I : Mod(𝒜, d)} (i : N ⟶ I)
    (hi : Module.quasiIso 𝒜 i) :
    ((toK 𝒜).obj M ⟶ (toK 𝒜).obj I) →
      ((Q 𝒜).obj M ⟶ (Q 𝒜).obj N) :=
  fun f ↦
    (Qh 𝒜).map f ≫
      (CategoryTheory.Localization.isoOfHom (Q 𝒜)
        (Module.quasiIso 𝒜) i hi).inv

/-- The represented map is localization of a homotopy class followed by the inverse of the
module-level localized replacement map. -/
theorem homToDerivedRep_apply (𝒜 : DGA(𝒪))
    {M N I : Mod(𝒜, d)} (i : N ⟶ I)
    (hi : Module.quasiIso 𝒜 i)
    (f : (toK 𝒜).obj M ⟶ (toK 𝒜).obj I) :
    homToDerivedRep 𝒜 i hi f =
      (Qh 𝒜).map f ≫
        (CategoryTheory.Localization.isoOfHom (Q 𝒜)
          (Module.quasiIso 𝒜) i hi).inv := sorry

/-- For represented DG modules, a quasi-isomorphism to a K-injective replacement computes
derived morphisms directly from intrinsic homotopy classes. -/
@[stacks 0FT8]
theorem homToDerivedRep_bijective (𝒜 : DGA(𝒪))
    {M N I : Mod(𝒜, d)} (i : N ⟶ I)
    (hi : Module.quasiIso 𝒜 i) [Module.IsKInjective I] :
    Function.Bijective (homToDerivedRep 𝒜 i hi :
      ((toK 𝒜).obj M ⟶ (toK 𝒜).obj I) →
        ((Q 𝒜).obj M ⟶ (Q 𝒜).obj N)) := sorry

end


end SheafOfModules.RingedSite.DifferentialGradedModule.DerivedCategory.KInjective
