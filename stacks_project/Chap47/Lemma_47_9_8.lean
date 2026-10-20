/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Category.ModuleCat.Ext.IdealPower.DerivedBaseChange
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.FlatBaseChange.Hom

open CategoryTheory

universe u

/- Lemma 47.9.8: flat base change inducing an isomorphism modulo a finitely
generated ideal gives bijections on every shifted Hom out of a complex with
ideal-power-torsion cohomology. -/
@[stacks 05EH] #check
  (CategoryTheory.ModuleCat.IdealPower.DerivedBaseChange.shiftedHomMap_bijective :
    ∀ {A B : Type u} [CommRing A] [CommRing B]
        (f : A →+* B) (I : Ideal A) (hI : I.FG) (hf : f.Flat)
        (hquot : Function.Bijective (f.quotientByIdeal I))
        (K : DerivedCategory.CohomologyIn
          (fun M : ModuleCat A ↦ Module.IsIdealPowerTorsion I M))
        (L : DerivedCategory (ModuleCat A)) (i : ℤ),
      Function.Bijective (fun e : ShiftedHom K.obj L i ↦
        e.map (ModuleCat.derivedExtensionOfScalars f)))

/- The module-level consequence identifies the canonical flat base-change map
on Ext in every degree when the source module is ideal-power torsion. -/
#check
  (CategoryTheory.ModuleCat.Ext.IdealPower.DerivedBaseChange.map_bijective :
    ∀ {A B : Type u} [CommRing A] [CommRing B]
        (f : A →+* B) (I : Ideal A) (hI : I.FG)
        (M N : ModuleCat.{u} A) (hf : f.Flat)
        (hM : Module.IsIdealPowerTorsion I M)
        (hquot : Function.Bijective (f.quotientByIdeal I)) (i : ℕ),
      Function.Bijective
        (CategoryTheory.ModuleCat.Ext.FlatBaseChange.map f M N hf i))
