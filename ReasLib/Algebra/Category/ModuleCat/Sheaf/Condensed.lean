/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

/-
  Canonical adapter from condensed modules to module sheaves on the coherent CompHaus site.

  The non-Prop data in this file is constructed from the native module sheafification API.
  The adapter retains the original additive sheaf and uses the native scalar extension
  and morphism construction.
-/

import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Condensed.Module
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafify
import ReasLib.AlgebraicGeometry.RingedSite.Basic
import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Sections

open CategoryTheory
open CategoryTheory.Functor
open Opposite
open scoped BigOperators

noncomputable section

universe u

namespace ReasLib.Condensed

abbrev Site := CompHaus.{u}
abbrev topology : GrothendieckTopology Site.{u} := coherentTopology Site.{u}

/-- The constant presheaf of rings used as coefficients. -/
abbrev constantRing (R : Type (u + 1)) [CommRing R] : Site.{u}ᵒᵖ ⥤ RingCat.{u + 1} :=
  (Functor.const Site.{u}ᵒᵖ).obj (RingCat.of R)

/-- The commutative constant ring sheaf and its underlying ring sheaf. -/
abbrev constantCommRingSheaf (R : Type (u + 1)) [CommRing R] :
    Sheaf topology.{u} CommRingCat.{u + 1} :=
  (constantSheaf topology.{u} CommRingCat.{u + 1}).obj (CommRingCat.of R)

abbrev constantRingSheaf (R : Type (u + 1)) [CommRing R] : Sheaf topology.{u} RingCat.{u + 1} :=
  Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (constantCommRingSheaf R)

/-- Forgetting commutativity preserves sheafification on the coherent CompHaus site.
This follows from the native characterization by local bijectivity, since forgetting
commutativity leaves the underlying maps of sections unchanged. -/
instance coefficientForget_preservesSheafification :
    topology.{u}.PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) where
  le P Q f hf := by
    change topology.{u}.W (Functor.whiskerRight f
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
    haveI : Presheaf.IsLocallyInjective topology.{u} f := hf.isLocallyInjective
    haveI : Presheaf.IsLocallySurjective topology.{u} f := hf.isLocallySurjective
    haveI : Presheaf.IsLocallyInjective topology.{u}
        (Functor.whiskerRight f (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) := by
      apply (Presheaf.isLocallyInjective_forget_iff topology.{u} _).mp
      change Presheaf.IsLocallyInjective topology.{u}
        (Functor.whiskerRight f (forget CommRingCat.{u + 1}))
      infer_instance
    haveI : Presheaf.IsLocallySurjective topology.{u}
        (Functor.whiskerRight f (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) := by
      apply (Presheaf.isLocallySurjective_iff_whisker_forget topology.{u} _).mpr
      change Presheaf.IsLocallySurjective topology.{u}
        (Functor.whiskerRight f (forget CommRingCat.{u + 1}))
      infer_instance
    exact topology.{u}.W_of_isLocallyBijective _

/-- The native commutative-ring sheafification unit, viewed as a map of ring presheaves. -/
noncomputable def coefficientMap (R : Type (u + 1)) [CommRing R] :
    constantRing R ⟶ (constantRingSheaf R).obj :=
  Functor.whiskerRight
    (toSheafify topology.{u}
      ((Functor.const Site.{u}ᵒᵖ).obj (CommRingCat.of R)))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

instance coefficientMap_isLocallyInjective (R : Type (u + 1)) [CommRing R] :
    Presheaf.IsLocallyInjective topology.{u} (coefficientMap R) := by
  apply (Presheaf.isLocallyInjective_forget_iff topology.{u} _).mp
  change Presheaf.IsLocallyInjective topology.{u}
    (Functor.whiskerRight
      (toSheafify topology.{u}
        ((Functor.const Site.{u}ᵒᵖ).obj (CommRingCat.of R)))
      (forget CommRingCat.{u + 1}))
  infer_instance

instance coefficientMap_isLocallySurjective (R : Type (u + 1)) [CommRing R] :
    Presheaf.IsLocallySurjective topology.{u} (coefficientMap R) := by
  apply (Presheaf.isLocallySurjective_iff_whisker_forget topology.{u} _).mpr
  change Presheaf.IsLocallySurjective topology.{u}
    (Functor.whiskerRight
      (toSheafify topology.{u}
        ((Functor.const Site.{u}ᵒᵖ).obj (CommRingCat.of R)))
      (forget CommRingCat.{u + 1}))
  infer_instance

/-- The original condensed module presheaf, with its genuine scalar restriction. -/
def modulePresheaf (R : Type (u + 1)) [CommRing R]
    (M : CondensedMod.{u} R) :
    PresheafOfModules.{u + 1} (constantRing R) where
  obj X := M.obj.obj X
  map {X Y} f :=
    M.obj.map f ≫
      (ModuleCat.restrictScalarsId'App ((constantRing R).map f).hom (by ext; rfl) (M.obj.obj Y)).inv
  map_id X := by
    ext x
    change (M.obj.map (𝟙 X)).hom x = x
    exact CategoryTheory.congr_fun (M.obj.map_id X) x
  map_comp f g := by
    ext x
    change (M.obj.map (f ≫ g)).hom x = (M.obj.map g).hom ((M.obj.map f).hom x)
    exact CategoryTheory.congr_fun (M.obj.map_comp f g) x

/-- The additive sheaf carrier obtained by the native forgetful sheaf composition. -/
noncomputable def additiveSheaf (R : Type (u + 1)) [CommRing R]
    (M : CondensedMod.{u} R) : Sheaf topology.{u} AddCommGrpCat.{u + 1} :=
  (sheafCompose topology.{u}
    (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).obj M

/-- The pointwise identity from the original module presheaf to its additive sheaf carrier. -/
def additiveComparison (R : Type (u + 1)) [CommRing R]
    (M : CondensedMod.{u} R) :
    (modulePresheaf R M).presheaf ⟶ (additiveSheaf R M).obj where
  app X := AddCommGrpCat.ofHom
    { toFun := fun x => x
      map_zero' := rfl
      map_add' := by intro x y; rfl }
  naturality X Y f := by
    ext x
    rfl

instance additiveComparison_isLocallyInjective (R : Type (u + 1)) [CommRing R]
    (M : CondensedMod.{u} R) :
    Presheaf.IsLocallyInjective topology.{u} (additiveComparison R M) := by
  apply Presheaf.isLocallyInjective_of_injective topology.{u} (additiveComparison R M)
  intro X x y h
  change x = y at h
  exact h

instance additiveComparison_isLocallySurjective (R : Type (u + 1)) [CommRing R]
    (M : CondensedMod.{u} R) :
    Presheaf.IsLocallySurjective topology.{u} (additiveComparison R M) := by
  apply Presheaf.isLocallySurjective_of_surjective topology.{u} (additiveComparison R M)
  intro X y
  exact ⟨y, rfl⟩

/-- The native sheaf of modules attached to a condensed module. -/
noncomputable def moduleSheaf (R : Type (u + 1)) [CommRing R]
    (M : CondensedMod.{u} R) :
    SheafOfModules.{u + 1} (constantRingSheaf R) :=
  PresheafOfModules.sheafify (coefficientMap R) (additiveComparison R M)

/-- The canonical comparison from the original module presheaf to the adapter. -/
noncomputable def comparison (R : Type (u + 1)) [CommRing R]
    (M : CondensedMod.{u} R) :
    modulePresheaf R M ⟶
      (PresheafOfModules.restrictScalars (coefficientMap R)).obj
        (moduleSheaf R M).val :=
  PresheafOfModules.toSheafify (coefficientMap R) (additiveComparison R M)

@[simp] theorem comparison_app_apply (R : Type (u + 1)) [CommRing R]
    (M : CondensedMod.{u} R) (X : Site.{u}ᵒᵖ) (x : (modulePresheaf R M).obj X) :
    ((comparison R M).app X).hom x = (additiveComparison R M).app X x :=
  PresheafOfModules.toSheafify_app_apply _ _ _ _

/-- The induced morphism on the original module presheaves. -/
def modulePresheafMap (R : Type (u + 1)) [CommRing R]
    {M N : CondensedMod.{u} R} (f : M ⟶ N) :
    modulePresheaf R M ⟶ modulePresheaf R N where
  app X := f.hom.app X
  naturality g := by
    ext x
    exact CondensedMod.hom_naturality_apply (R := R) f g x

/-- The induced map on the additive sheaf carriers. -/
noncomputable def additiveSheafMap (R : Type (u + 1)) [CommRing R]
    {M N : CondensedMod.{u} R} (f : M ⟶ N) :
    additiveSheaf R M ⟶ additiveSheaf R N :=
  (sheafCompose topology.{u}
    (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).map f

/-- The native sheafification map induced by a condensed-module morphism. -/
noncomputable def moduleSheafMap (R : Type (u + 1)) [CommRing R]
    {M N : CondensedMod.{u} R} (f : M ⟶ N) :
    moduleSheaf R M ⟶ moduleSheaf R N :=
  PresheafOfModules.sheafifyMap (coefficientMap R)
    (additiveComparison R M) (additiveComparison R N)
    (modulePresheafMap R f) (additiveSheafMap R f) (by
      ext X x
      rfl)

/-- The functor on objects and morphisms. -/
noncomputable def functor (R : Type (u + 1)) [CommRing R] :
    CondensedMod.{u} R ⥤ SheafOfModules.{u + 1} (constantRingSheaf R) where
  obj := moduleSheaf R
  map := moduleSheafMap R
  map_id M := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro X
    ext x
    rfl
  map_comp f g := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro X
    ext x
    rfl

/-- The ULifted-integer specialization, i.e. the condensed abelian-group adapter. -/
abbrev condensedAbFunctor : CondensedAb.{u} ⥤
    SheafOfModules.{u + 1} (constantRingSheaf (ULift.{u + 1} ℤ)) :=
  functor (ULift.{u + 1} ℤ)

/-- Naturality of the comparison with respect to a condensed-module morphism. -/
theorem comparison_naturality (R : Type (u + 1)) [CommRing R]
    {M N : CondensedMod.{u} R} (f : M ⟶ N) (X : Site.{u}ᵒᵖ)
    (x : (modulePresheaf R M).obj X) :
    ((comparison R N).app X).hom ((modulePresheafMap R f).app X x) =
      ((moduleSheafMap R f).val.app X).hom ((comparison R M).app X x) := by
  rfl

end ReasLib.Condensed
