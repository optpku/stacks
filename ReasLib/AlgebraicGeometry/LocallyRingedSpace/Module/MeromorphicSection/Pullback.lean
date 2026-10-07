module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.MeromorphicFunction.Pullback
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.Basic
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.RegularMeromorphicSection
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Composition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Sections
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InvertiblePullback

/-!
# Pullback of meromorphic sections

A morphism of locally ringed spaces that preserves meromorphic denominators induces pullback on
meromorphic functions and on meromorphic sections. The comparison with extension of scalars also
shows that regular meromorphic sections of invertible modules remain regular after pullback.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open Opposite
open SheafOfModules.RingedSite
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X Y : LocallyRingedSpace.{u}}

namespace Hom

/-- Pullback of the meromorphic-section sheaf is canonically identified with meromorphic
extension of the pulled-back module sheaf. -/
noncomputable def pullbackMeromorphicSectionSheafIso
    (f : X ⟶ Y) (hf : Hom.pullbacksRegularMeromorphicFunctionsDefined f)
    (ℱ : Y.Modules) :
    (RingedSpace.Hom.pullback
      (Hom.meromorphicFunctionRingedSpaceHom f hf)).obj
        (Y.meromorphicSectionSheaf ℱ) ≅
      X.meromorphicSectionSheaf ((RingedSpace.Hom.pullback f.toShHom).obj ℱ) :=
  let toMeromorphicX :
      X.meromorphicFunctionSheaf.toRingedSpace ⟶ X.toRingedSpace :=
    SheafedSpace.fullyFaithfulForgetToPresheafedSpace.preimage
      { base := 𝟙 X.toTopCat
        c := X.toMeromorphicFunctionSheafHom.hom }
  let toMeromorphicY :
      Y.meromorphicFunctionSheaf.toRingedSpace ⟶ Y.toRingedSpace :=
    SheafedSpace.fullyFaithfulForgetToPresheafedSpace.preimage
      { base := 𝟙 Y.toTopCat
        c := Y.toMeromorphicFunctionSheafHom.hom }
  let comm : Hom.meromorphicFunctionRingedSpaceHom f hf ≫ toMeromorphicY =
      toMeromorphicX ≫ f.toShHom := by
    refine SheafedSpace.ext
      (Hom.meromorphicFunctionRingedSpaceHom f hf ≫ toMeromorphicY)
      (toMeromorphicX ≫ f.toShHom) rfl ?_
    ext U x
    convert congrArg (fun k ↦ (k.hom.app (op U)).hom x)
      (Hom.toMeromorphicFunctionSheafHom_naturality f hf) using 1 <;>
        simp [toMeromorphicX, toMeromorphicY,
          Hom.meromorphicFunctionRingedSpaceHom] <;>
        try rfl
    apply heq_of_eq
    have hU : (Opens.map (𝟙 Y.toTopCat)).obj U = U :=
      Opens.map_id_obj U
    let i : op ((Opens.map (𝟙 Y.toTopCat)).obj U) ⟶ op U :=
      eqToHom (congrArg op hU)
    have hi := (Hom.meromorphicFunctionSheafMap f hf).hom.naturality i
    have hj := Y.toMeromorphicFunctionSheafHom.hom.naturality i
    have hcomp :
        Y.toMeromorphicFunctionSheafHom.hom.app
              (op ((Opens.map (𝟙 Y.toTopCat)).obj U)) ≫
            (Hom.meromorphicFunctionSheafMap f hf).hom.app
              (op ((Opens.map (𝟙 Y.toTopCat)).obj U)) ≫
            ((TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj
              X.meromorphicFunctionSheaf).obj.map i =
          Y.𝒪.obj.map i ≫ Y.toMeromorphicFunctionSheafHom.hom.app (op U) ≫
            (Hom.meromorphicFunctionSheafMap f hf).hom.app (op U) := by
      rw [← hi, ← Category.assoc, ← hj, Category.assoc]
    convert congrArg (fun k ↦ k.hom x) hcomp using 1
    · simp_all [toMeromorphicX]
    · cases hU
      have i_eq : i = 𝟙 (op U) := Subsingleton.elim _ _
      rw [i_eq]
      apply heq_of_eq
      congr 1
    · let U' : (Opens Y.toTopCat)ᵒᵖ := op U
      have hmap : Y.𝒪.presheaf.map (𝟙 U') = 𝟙 _ :=
        Y.𝒪.presheaf.map_id U'
      have hcat' :
          Y.𝒪.presheaf.map (𝟙 U') ≫
              Y.toMeromorphicFunctionSheafHom.hom.app U' ≫
              (Hom.meromorphicFunctionSheafMap f hf).hom.app U' =
            Y.toMeromorphicFunctionSheafHom.hom.app U' ≫
              (Hom.meromorphicFunctionSheafMap f hf).hom.app U' := by
        rw [hmap, Category.id_comp]
      cases hU
      have i_eq : i = 𝟙 (op U) := Subsingleton.elim _ _
      rw [i_eq]
      apply heq_of_eq
      congr 1
      exact congrArg CommRingCat.Hom.hom hcat'.symm
  (((RingedSpace.Hom.pullbackCompIso toMeromorphicX f.toShHom).symm ≪≫
    eqToIso (congrArg RingedSpace.Hom.pullback
      comm.symm) ≪≫
    RingedSpace.Hom.pullbackCompIso
      (Hom.meromorphicFunctionRingedSpaceHom f hf)
      toMeromorphicY).app ℱ).symm

/-- Pull back a meromorphic section along a morphism that preserves meromorphic denominators. -/
noncomputable def pullbackMeromorphicSections
    (f : X ⟶ Y) (hf : Hom.pullbacksRegularMeromorphicFunctionsDefined f)
    (ℱ : Y.Modules) :
    Y.meromorphicSections ℱ →
      X.meromorphicSections ((RingedSpace.Hom.pullback f.toShHom).obj ℱ) :=
  fun s ↦ SheafOfModules.sectionsMap
    (Hom.pullbackMeromorphicSectionSheafIso f hf ℱ).hom
    (RingedSpace.Hom.pullbackSections
      (Hom.meromorphicFunctionRingedSpaceHom f hf) s)

/-- Pullback of meromorphic sections is natural in the module sheaf. -/
theorem pullbackMeromorphicSections_naturality
    (f : X ⟶ Y) (hf : Hom.pullbacksRegularMeromorphicFunctionsDefined f)
    {ℱ 𝒢 : Y.Modules} (φ : ℱ ⟶ 𝒢) (s : Y.meromorphicSections ℱ) :
    Hom.pullbackMeromorphicSections f hf 𝒢
        (SheafOfModules.sectionsMap
          ((Y.meromorphicSectionSheafFunctor).map φ) s) =
      SheafOfModules.sectionsMap
        ((X.meromorphicSectionSheafFunctor).map
          ((RingedSpace.Hom.pullback f.toShHom).map φ))
        (Hom.pullbackMeromorphicSections f hf ℱ s) := sorry

end Hom

namespace IsRegularMeromorphicSection

/-- Pullback along a morphism preserving meromorphic denominators carries a regular
meromorphic section of an invertible module to a regular meromorphic section. -/
theorem pullback
    (f : X ⟶ Y) (hf : Hom.pullbacksRegularMeromorphicFunctionsDefined f)
    (ℒ : Y.Modules) [MonoidalCategory.isInvertibleObject ℒ]
    (s : Y.meromorphicSections ℒ) (hs : Y.IsRegularMeromorphicSection ℒ s) :
    X.IsRegularMeromorphicSection ((RingedSpace.Hom.pullback f.toShHom).obj ℒ)
      (Hom.pullbackMeromorphicSections f hf ℒ s) := sorry

end IsRegularMeromorphicSection

end AlgebraicGeometry.LocallyRingedSpace
