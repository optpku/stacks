module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite

/-!
# Restriction of module-sheaf sections on ringed sites

This leaf exposes the ordinary restriction maps on sections of a module sheaf over a ringed
site, together with their basic functoriality.  It is independent of topology-specific covering
or finiteness hypotheses.
-/

@[expose] public section

open CategoryTheory
open Opposite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable (𝒪 : Sheaf J CommRingCat.{max u v})

/-- Restrict a section of a module sheaf along a morphism in the underlying site. -/
def sectionRestriction {U V : C} (f : V ⟶ U) (ℱ : ringedSiteModuleCategory J 𝒪) :
    (SheafOfModules.evaluation (ringSheaf J 𝒪) (op U)).obj ℱ →
      (SheafOfModules.evaluation (ringSheaf J 𝒪) (op V)).obj ℱ :=
  ((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ).1.map f.op

/-- Restriction of sections commutes with the map induced by a module-sheaf morphism. -/
theorem sectionRestriction_naturality
    {U V : C} {ℱ 𝒢 : ringedSiteModuleCategory J 𝒪}
    (f : V ⟶ U) (α : ℱ ⟶ 𝒢)
    (s : (SheafOfModules.evaluation (ringSheaf J 𝒪) (op U)).obj ℱ) :
    ((SheafOfModules.evaluation (ringSheaf J 𝒪) (op V)).map α)
        (sectionRestriction J 𝒪 f ℱ s) =
      sectionRestriction J 𝒪 f 𝒢
        (((SheafOfModules.evaluation (ringSheaf J 𝒪) (op U)).map α) s) := sorry

/-- Two successive restrictions of module-sheaf sections equal restriction along their
composite. -/
theorem sectionRestriction_comp
    {U V W : C} (f : U ⟶ V) (g : V ⟶ W) (ℱ : ringedSiteModuleCategory J 𝒪)
    (s : (SheafOfModules.evaluation (ringSheaf J 𝒪) (op W)).obj ℱ) :
    sectionRestriction J 𝒪 f ℱ (sectionRestriction J 𝒪 g ℱ s) =
      sectionRestriction J 𝒪 (f ≫ g) ℱ s := sorry

end SheafOfModules.RingedSite
