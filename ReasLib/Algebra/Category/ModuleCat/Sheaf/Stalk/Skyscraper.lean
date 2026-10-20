/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Stalk.Skyscraper
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk
public import Mathlib.Topology.Sheaves.Skyscraper
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Skyscraper sheaves of modules and stalks

This file bundles the module-presheaf skyscraper as a sheaf and lifts the
stalk-skyscraper adjunction to sheaves of modules.  The construction is the
module-valued counterpart of `TopCat.skyscraperSheaf`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf TopCat TopologicalSpace

noncomputable section

universe u

namespace PresheafOfModules.Skyscraper

variable {X : TopCat.{u}}

/-- The underlying additive presheaf of the module skyscraper satisfies the sheaf condition. -/
theorem atPoint_isSheaf (R : X.Sheaf CommRingCat.{u}) (x : X)
    (N : ModuleCat.{u} (R.presheaf.stalk x)) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (atPoint R.presheaf x N).presheaf := sorry

/-- The skyscraper sheaf of modules over `R`, supported at `x` with stalk-module value `N`. -/
@[stacks 007K "skyscraper sheaf of modules"]
noncomputable def sheafAtPoint (R : X.Sheaf CommRingCat.{u}) (x : X)
    (N : ModuleCat.{u} (R.presheaf.stalk x)) :
    SheafOfModules.{u} (TopCat.Sheaf.ringSheafOfComm R) where
  val := atPoint R.presheaf x N
  isSheaf := atPoint_isSheaf R x N

/-- A map of stalk modules induces a morphism of skyscraper sheaves of modules. -/
noncomputable def sheafMapHom (R : X.Sheaf CommRingCat.{u}) (x : X)
    {N N' : ModuleCat.{u} (R.presheaf.stalk x)} (f : N ⟶ N') :
    sheafAtPoint R x N ⟶ sheafAtPoint R x N' :=
  ⟨mapHom R.presheaf x f⟩

/-- Skyscraper sheaves send identity stalk maps to identity morphisms. -/
theorem sheafMapHom_id (R : X.Sheaf CommRingCat.{u}) (x : X)
    (N : ModuleCat.{u} (R.presheaf.stalk x)) :
    sheafMapHom R x (𝟙 N) = 𝟙 (sheafAtPoint R x N) := sorry

/-- Skyscraper sheaves send composites of stalk maps to composites. -/
theorem sheafMapHom_comp (R : X.Sheaf CommRingCat.{u}) (x : X)
    {N N' N'' : ModuleCat.{u} (R.presheaf.stalk x)} (f : N ⟶ N') (g : N' ⟶ N'') :
    sheafMapHom R x (f ≫ g) = sheafMapHom R x f ≫ sheafMapHom R x g := sorry

/-- The skyscraper functor from stalk modules to sheaves of modules. -/
@[stacks 007K "skyscraper functor for sheaves of modules"]
noncomputable def sheafFunctorOfCommRing (R : X.Sheaf CommRingCat.{u}) (x : X) :
    ModuleCat.{u} (R.presheaf.stalk x) ⥤
      SheafOfModules.{u} (TopCat.Sheaf.ringSheafOfComm R) where
  obj := sheafAtPoint R x
  map := sheafMapHom R x
  map_id := sheafMapHom_id R x
  map_comp := sheafMapHom_comp R x

/-- Passing from a sheaf-stalk map to a skyscraper-sheaf map and back recovers the stalk map. -/
theorem sheafFrom_to (R : X.Sheaf CommRingCat.{u}) (x : X)
    {F : SheafOfModules.{u} (TopCat.Sheaf.ringSheafOfComm R)}
    {N : ModuleCat.{u} (R.presheaf.stalk x)}
    (f : (SheafOfModules.stalkFunctorOfCommRing R x).obj F ⟶ N) :
    fromHom R.presheaf x (toHom R.presheaf x f) = f := sorry

/-- Passing from a skyscraper-sheaf map to a sheaf-stalk map and back recovers the sheaf map. -/
theorem sheafTo_from (R : X.Sheaf CommRingCat.{u}) (x : X)
    {F : SheafOfModules.{u} (TopCat.Sheaf.ringSheafOfComm R)}
    {N : ModuleCat.{u} (R.presheaf.stalk x)} (g : F ⟶ sheafAtPoint R x N) :
    ⟨toHom R.presheaf x (fromHom R.presheaf x g.val)⟩ = g := sorry

/-- Maps from the stalk of a module sheaf to `N` are equivalent to maps from the sheaf to the
skyscraper sheaf of `N`. -/
@[stacks 007K "module-sheaf stalk-skyscraper Hom equivalence"]
noncomputable def sheafHomEquiv (R : X.Sheaf CommRingCat.{u}) (x : X)
    (F : SheafOfModules.{u} (TopCat.Sheaf.ringSheafOfComm R))
    (N : ModuleCat.{u} (R.presheaf.stalk x)) :
    ((SheafOfModules.stalkFunctorOfCommRing R x).obj F ⟶ N) ≃
      (F ⟶ sheafAtPoint R x N) where
  toFun f := ⟨toHom R.presheaf x f⟩
  invFun g := fromHom R.presheaf x g.val
  left_inv := sheafFrom_to R x
  right_inv := sheafTo_from R x

/-- The inverse sheaf-stalk/skyscraper equivalence is natural in the module sheaf. -/
theorem sheafHomEquiv_naturality_left_symm (R : X.Sheaf CommRingCat.{u}) (x : X)
    {F G : SheafOfModules.{u} (TopCat.Sheaf.ringSheafOfComm R)}
    {N : ModuleCat.{u} (R.presheaf.stalk x)} (f : F ⟶ G)
    (g : G ⟶ sheafAtPoint R x N) :
    (sheafHomEquiv R x F N).symm (f ≫ g) =
      (SheafOfModules.stalkFunctorOfCommRing R x).map f ≫
        (sheafHomEquiv R x G N).symm g := sorry

/-- The sheaf-stalk/skyscraper equivalence is natural in the stalk module. -/
theorem sheafHomEquiv_naturality_right (R : X.Sheaf CommRingCat.{u}) (x : X)
    {F : SheafOfModules.{u} (TopCat.Sheaf.ringSheafOfComm R)}
    {N N' : ModuleCat.{u} (R.presheaf.stalk x)}
    (f : (SheafOfModules.stalkFunctorOfCommRing R x).obj F ⟶ N) (g : N ⟶ N') :
    sheafHomEquiv R x F N' (f ≫ g) =
      sheafHomEquiv R x F N f ≫ sheafMapHom R x g := sorry

/-- The stalk functor on sheaves of modules is left adjoint to the skyscraper-sheaf functor. -/
@[stacks 007K "module-sheaf stalk-skyscraper adjunction"]
noncomputable def sheafAdjunctionOfCommRing (R : X.Sheaf CommRingCat.{u}) (x : X) :
    SheafOfModules.stalkFunctorOfCommRing R x ⊣ sheafFunctorOfCommRing R x :=
  Adjunction.mkOfHomEquiv
    { homEquiv := sheafHomEquiv R x
      homEquiv_naturality_left_symm := sheafHomEquiv_naturality_left_symm R x
      homEquiv_naturality_right := sheafHomEquiv_naturality_right R x }

end PresheafOfModules.Skyscraper
