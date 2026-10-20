/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Differentials
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Free
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Free

/-!
# Groupoid-scheme differentials over fields

This module establishes freeness of the identity conormal sheaf and the target-relative
differentials when the object scheme is the spectrum of a field.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The conormal sheaf of the identity section of a groupoid scheme is free when the object
scheme is isomorphic to the spectrum of a field. -/
theorem identityConormal_isFreeOfSpecField {S : Scheme.{u}} (G : GroupoidScheme S)
    {k : Type u} [Field k] (eU : Spec (CommRingCat.of k) ≅ G.U.left) :
    SheafOfModules.IsFree (Scheme.Hom.conormalSheaf G.e.left) := by
  let F := (Scheme.Modules.restrictFunctor eU.hom).obj
    (Scheme.Hom.conormalSheaf G.e.left)
  have hRestricted : SheafOfModules.IsFree F := by
    -- Local instance justification (proof-local temporary data): quasicoherence is installed
    -- only to apply affine reconstruction to the restricted conormal sheaf.
    let _ : F.IsQuasicoherent :=
      @Scheme.Modules.isQuasicoherent_restrictFunctor _ _ eU.hom
        (inferInstance) (Scheme.Hom.conormalSheaf G.e.left)
          (@Scheme.Hom.conormalSheaf_isQuasicoherent _ _ G.e.left
            (Differentials.identity_isImmersion G))
    -- Local instance justification (proof-local temporary data): vector-space freeness is
    -- installed only for the global sections of this affine quasicoherent sheaf.
    let _ : Module.Free k
        ((AlgebraicGeometry.moduleSpecΓFunctor (R := CommRingCat.of k)).obj F) :=
      Module.Free.of_divisionRing k
        ((AlgebraicGeometry.moduleSpecΓFunctor (R := CommRingCat.of k)).obj F)
    infer_instance
  -- Local instance justification (proof-local temporary data): restricted freeness is installed
  -- only while transporting it back across the inverse object-scheme isomorphism.
  let _ : SheafOfModules.IsFree F := hRestricted
  have hPulledBack :
      SheafOfModules.IsFree ((Scheme.Modules.restrictFunctor eU.inv).obj F) := by
    infer_instance
  -- Local instance justification (proof-local temporary data): pullback freeness is installed
  -- only for transport across the restriction composition isomorphism.
  let _ : SheafOfModules.IsFree ((Scheme.Modules.restrictFunctor eU.inv).obj F) := hPulledBack
  let E : (Scheme.Modules.restrictFunctor eU.inv).obj F ≅
      Scheme.Hom.conormalSheaf G.e.left :=
    ((Scheme.Modules.restrictFunctorComp eU.inv eU.hom).app
      (Scheme.Hom.conormalSheaf G.e.left)).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr eU.inv_hom_id).app
        (Scheme.Hom.conormalSheaf G.e.left) ≪≫
      (Scheme.Modules.restrictFunctorId (X := G.U.left)).app
        (Scheme.Hom.conormalSheaf G.e.left)
  exact SheafOfModules.IsFree.of_iso E

/-- The relative differential sheaf of the target map of a groupoid scheme is free when the
object scheme is isomorphic to the spectrum of a field. -/
theorem targetDifferentials_isFreeOfSpecField {S : Scheme.{u}} (G : GroupoidScheme S)
    {k : Type u} [Field k] (eU : Spec (CommRingCat.of k) ≅ G.U.left) :
    SheafOfModules.IsFree Ω[G.t.left.toShHom] := by
  have hToSpec : Flat (G.s.left ≫ eU.inv) := by
    infer_instance
  have hSourceFlat : Flat G.s.left := by
    simpa using
      (CategoryTheory.MorphismProperty.cancel_right_of_respectsIso
        (P := @Flat) (G.s.left ≫ eU.inv) eU.hom).2 hToSpec
  -- Local instance justification (proof-local temporary data): source flatness is derived from
  -- the field-valued composite only to invoke the conormal comparison theorem.
  let _ : Flat G.s.left := hSourceFlat
  have hConormal : SheafOfModules.IsFree (Scheme.Hom.conormalSheaf G.e.left) :=
    identityConormal_isFreeOfSpecField G eU
  -- Local instance justification (proof-local temporary data): conormal freeness is installed
  -- only while pulling the sheaf back along the target map.
  let _ : SheafOfModules.IsFree (Scheme.Hom.conormalSheaf G.e.left) := hConormal
  have hPullback :
      SheafOfModules.IsFree
        ((Scheme.Modules.pullback G.t.left).obj (Scheme.Hom.conormalSheaf G.e.left)) := by
    rcases SheafOfModules.IsFree.exists_iso_free
        (F := Scheme.Hom.conormalSheaf G.e.left) with ⟨I, ⟨e⟩⟩
    let eMap :
        (SheafOfModules.pullback G.t.left.toRingCatSheafHom).obj
            (Scheme.Hom.conormalSheaf G.e.left) ≅
          (SheafOfModules.pullback G.t.left.toRingCatSheafHom).obj
            (SheafOfModules.free I : G.U.left.Modules) :=
      (SheafOfModules.pullback G.t.left.toRingCatSheafHom).mapIso e
    let eFree :
        (SheafOfModules.pullback G.t.left.toRingCatSheafHom).obj
            (SheafOfModules.free I : G.U.left.Modules) ≅
          (SheafOfModules.free I : G.R.left.Modules) :=
      AlgebraicGeometry.RingedSpace.Hom.pullbackFreeIso G.t.left.toShHom I
    change SheafOfModules.IsFree
      ((SheafOfModules.pullback G.t.left.toRingCatSheafHom).obj
        (Scheme.Hom.conormalSheaf G.e.left))
    exact SheafOfModules.IsFree.of_iso (eMap ≪≫ eFree).symm
  -- Local instance justification (proof-local temporary data): pullback freeness is installed
  -- only for transport across the groupoid conormal comparison.
  let _ : SheafOfModules.IsFree
      ((Scheme.Modules.pullback G.t.left).obj (Scheme.Hom.conormalSheaf G.e.left)) := hPullback
  let hIso : IsIso (Differentials.conormalComparison G) :=
    Differentials.conormalComparison_isIso G
  let eComparison :
      (Scheme.Modules.pullback G.t.left).obj (Scheme.Hom.conormalSheaf G.e.left) ≅
        Ω[G.t.left.toShHom] :=
    @asIso _ _ _ _ (Differentials.conormalComparison G) hIso
  exact SheafOfModules.IsFree.of_iso eComparison

end AlgebraicGeometry.GroupoidScheme
