/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.DifferentialGraded

/-!
# The underlying cochain homotopy functor

This leaf compares the homotopy category of differential graded module sheaves with the
ordinary homotopy category of their underlying cochain complexes.  It is independent of
homology and of any triangulated structure.
-/

@[expose] public section

open CategoryTheory
open ComplexShape
open DifferentialGradedCategory
open scoped DifferentialGradedCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedModule

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

-- Local declaration justification (parser conflict): this alias only shortens the canonical
-- module-sheaf category and avoids another public notation beside `Mod(𝒜, d)`.
local notation "ModO" => ringedSiteModuleCategory J 𝒪

namespace Homotopy

/-- A DG-module homotopy forgets to an ordinary homotopy between the underlying cochain
maps. -/
theorem underlying_homotopy
    {𝒜 : DGA(𝒪)} {L M : Mod(𝒜, d)} {f g : CompHom L M}
    (h : Homotopic L M f g) :
    Nonempty
      (_root_.Homotopy
        (compHomToHom f).toCochainMap
        (compHomToHom g).toCochainMap) := sorry

/-- Homotopic closed DG-module maps induce the same morphism between their underlying
cochain complexes in the ordinary homotopy category. -/
theorem forget_map_sound
    {𝒜 : DGA(𝒪)} {L M : Mod(𝒜, d)} {f g : CompHom L M}
    (h : Homotopic L M f g) :
    (HomotopyCategory.quotient ModO (up ℤ)).map
        (compHomToHom f).toCochainMap =
      (HomotopyCategory.quotient ModO (up ℤ)).map
        (compHomToHom g).toCochainMap := sorry

/-- Forget the DG-algebra action on the homotopy category and retain the underlying cochain
complex up to ordinary cochain homotopy. -/
def forget (𝒜 : DGA(𝒪)) :
    K ℤ Mod(𝒜, d) ⥤
      HomotopyCategory
        (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) (up ℤ) where
  obj X :=
    (HomotopyCategory.quotient
      (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) (up ℤ)).obj
      X.obj.toComplex
  map {X Y} f :=
    _root_.Quotient.lift
      (fun g : CompHom X.obj Y.obj ↦
        (HomotopyCategory.quotient ModO (up ℤ)).map
          (compHomToHom g).toCochainMap)
      (fun _ _ h ↦ forget_map_sound h)
      f
  map_id := sorry
  map_comp := sorry

/-- The underlying homotopy functor sends a DG-module object to its underlying cochain
complex in the ordinary homotopy category. -/
@[simp]
theorem forget_obj (𝒜 : DGA(𝒪)) (X : K ℤ Mod(𝒜, d)) :
    (forget 𝒜).obj X =
      (HomotopyCategory.quotient ModO (up ℤ)).obj X.obj.toComplex := sorry

/-- The underlying homotopy functor maps a represented DG homotopy class by forgetting the
action and taking the ordinary cochain-homotopy class. -/
@[simp]
theorem forget_map_rep
    (𝒜 : DGA(𝒪)) {L M : Mod(𝒜, d)} (f : CompHom L M) :
    (forget 𝒜).map f.toHomotopyClass =
      (HomotopyCategory.quotient ModO (up ℤ)).map
        (compHomToHom f).toCochainMap := sorry

/-- Forgetting from the DG homotopy category to the ordinary cochain homotopy category is
additive. -/
instance forget_additive (𝒜 : DGA(𝒪)) :
    (forget 𝒜).Additive := sorry

/-- The underlying homotopy functor factors the ordinary forgetful functor through the
closed degree-zero presentation and the DG homotopy quotient. -/
noncomputable def forgetFactors (𝒜 : DGA(𝒪)) :
    toK 𝒜 ⋙ forget 𝒜 ≅
      forgetToComplex 𝒜 ⋙ HomotopyCategory.quotient ModO (up ℤ) where
  hom :=
    { app := fun M ↦ 𝟙 ((HomotopyCategory.quotient ModO (up ℤ)).obj M.toComplex)
      naturality := sorry }
  inv :=
    { app := fun M ↦ 𝟙 ((HomotopyCategory.quotient ModO (up ℤ)).obj M.toComplex)
      naturality := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward component of `forgetFactors` is the identity. -/
@[simp]
theorem forgetFactors_hom_app
    (𝒜 : DGA(𝒪)) (M : Mod(𝒜, d)) :
    (forgetFactors 𝒜).hom.app M =
      𝟙 ((HomotopyCategory.quotient ModO (up ℤ)).obj M.toComplex) := sorry

end Homotopy

end

end SheafOfModules.RingedSite.DifferentialGradedModule
