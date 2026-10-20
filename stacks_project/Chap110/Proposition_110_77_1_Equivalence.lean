/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Localization.SerreQuotient

/-!
# Serre quotient of modules by S-torsion

The exact localization functor `ModuleCat R ⥤ ModuleCat (Localization S)` descends uniquely
through the Serre quotient by `S`-torsion. Restriction of scalars, followed by the Serre
quotient functor, is the canonical inverse on objects.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ObjectProperty

noncomputable section

universe v u

namespace ModuleCat

variable {R : Type u} [CommRing R] [Small.{v} R] (S : Submonoid R)

#check (ModuleCat.localizedExactFunctor S :
  ModuleCat.{v} R ⥤ₑ ModuleCat.{v} (Localization S))

#check (CategoryTheory.ExactFunctor.of_fst (ModuleCat.localizedModuleFunctor.{v} S) :
  (ModuleCat.localizedExactFunctor S).obj = ModuleCat.localizedModuleFunctor.{v} S)

#check (ModuleCat.inducedLocalizedFunctor S :
  (ModuleCat.isTorsion' S).isoModSerre.Localization ⥤ ModuleCat.{v} (Localization S))

#check (ModuleCat.quotientRestrictScalars S :
  ModuleCat.{v} (Localization S) ⥤ (ModuleCat.isTorsion' S).isoModSerre.Localization)

#check (ModuleCat.inducedLocalizedFunctor_fac S :
  (ModuleCat.isTorsion' S).isoModSerre.Q ⋙ ModuleCat.inducedLocalizedFunctor S ≅
    ModuleCat.localizedModuleFunctor.{v} S)

#check (CategoryTheory.Iso.hom_inv_id (ModuleCat.inducedLocalizedFunctor_fac S) :
  (ModuleCat.inducedLocalizedFunctor_fac S).hom ≫
      (ModuleCat.inducedLocalizedFunctor_fac S).inv =
    𝟙 ((ModuleCat.isTorsion' S).isoModSerre.Q ⋙ ModuleCat.inducedLocalizedFunctor S))

#check (ModuleCat.quotientRestrictScalars_obj S :
  ∀ N : ModuleCat.{v} (Localization S),
    (ModuleCat.quotientRestrictScalars S).obj N =
      (ModuleCat.isTorsion' S).isoModSerre.Q.obj
        ((ModuleCat.restrictScalars (algebraMap R (Localization S))).obj N))

#check (ModuleCat.inducedLocalizedFunctor_isEquivalence S :
  (ModuleCat.inducedLocalizedFunctor S).IsEquivalence)

#check (ModuleCat.instIsEquivalenceInducedLocalizedFunctor S :
  (ModuleCat.inducedLocalizedFunctor S).IsEquivalence)

end ModuleCat
