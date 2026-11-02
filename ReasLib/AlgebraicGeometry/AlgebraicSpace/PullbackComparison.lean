/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Diagonal

/-!
# Geometric properties of fibre-product comparisons

For morphisms `f : X ⟶ Z`, `g : Y ⟶ Z`, and `h : Z ⟶ T` of algebraic spaces over a
scheme, the canonical comparison `X ×_Z Y ⟶ X ×_T Y` is representable, locally of
finite type, locally quasi-finite, separated, and a monomorphism. Separation
properties of `h` imply stronger immersion and quasi-compactness properties.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Transfer a base-change-stable property of the presheaf diagonal to the comparison
between the chosen algebraic-space pullbacks. -/
private theorem mapDesc_property_of_diagonal {S : Scheme.{u}}
    {X Y Z T : AlgebraicSpace S} (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T)
    (P : MorphismProperty ((Over S)ᵒᵖ ⥤ Type u)) [P.IsStableUnderBaseChange]
    (hh : P (pullback.diagonal (C := (Over S)ᵒᵖ ⥤ Type u) h)) :
    P (pullback.mapDesc f g h) := by
  let sq := ReasLibPullback.isPullback f g
  let sq' := ReasLibPullback.isPullback (f ≫ h) (g ≫ h)
  let e : (pullback f g).functorOfPoints ≅
      pullback (C := (Over S)ᵒᵖ ⥤ Type u) f g :=
    { hom := sq.isoPullback.inv
      inv := sq.isoPullback.hom
      hom_inv_id := sq.isoPullback.inv_hom_id
      inv_hom_id := sq.isoPullback.hom_inv_id }
  let e' : (pullback (f ≫ h) (g ≫ h)).functorOfPoints ≅
      pullback (C := (Over S)ᵒᵖ ⥤ Type u) (f ≫ h) (g ≫ h) :=
    { hom := sq'.isoPullback.inv
      inv := sq'.isoPullback.hom
      hom_inv_id := sq'.isoPullback.inv_hom_id
      inv_hom_id := sq'.isoPullback.hom_inv_id }
  let d : (pullback f g).functorOfPoints ⟶
      (pullback (f ≫ h) (g ≫ h)).functorOfPoints :=
    pullback.mapDesc (C := AlgebraicSpace S) f g h
  have hw : e.hom ≫ pullback.mapDesc (C := (Over S)ᵒᵖ ⥤ Type u) f g h =
      d ≫ e'.hom := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, Category.comp_id]
      rw [show e.hom ≫ pullback.fst (C := (Over S)ᵒᵖ ⥤ Type u) f g =
        (pullback.fst f g : pullback f g ⟶ X) from sq.isoPullback_inv_fst,
        show e'.hom ≫ pullback.fst (C := (Over S)ᵒᵖ ⥤ Type u) (f ≫ h) (g ≫ h) =
          (pullback.fst (f ≫ h) (g ≫ h) : pullback (f ≫ h) (g ≫ h) ⟶ X) from
            sq'.isoPullback_inv_fst]
      exact (Category.comp_id (pullback.fst f g)).symm.trans
        (pullback.lift_fst (C := AlgebraicSpace S) _ _ _).symm
    · simp only [Category.assoc, pullback.lift_snd, Category.comp_id]
      rw [show e.hom ≫ pullback.snd (C := (Over S)ᵒᵖ ⥤ Type u) f g =
        (pullback.snd f g : pullback f g ⟶ Y) from sq.isoPullback_inv_snd,
        show e'.hom ≫ pullback.snd (C := (Over S)ᵒᵖ ⥤ Type u) (f ≫ h) (g ≫ h) =
          (pullback.snd (f ≫ h) (g ≫ h) : pullback (f ≫ h) (g ≫ h) ⟶ Y) from
            sq'.isoPullback_inv_snd]
      exact (Category.comp_id (pullback.snd f g)).symm.trans
        (pullback.lift_snd (C := AlgebraicSpace S) _ _ _).symm
  change P d
  apply (P.arrow_mk_iso_iff (Arrow.isoMk e e' hw)).mpr
  exact MorphismProperty.of_isPullback
    (pullback_map_diagonal_isPullback (C := (Over S)ᵒᵖ ⥤ Type u) f g h) hh

/-- The canonical fibre-product comparison induced by a morphism of algebraic spaces
is representable. -/
theorem relativelyRepresentable_mapDesc {S : Scheme.{u}} {X Y Z T : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) :
    yoneda.relativelyRepresentable (pullback.mapDesc f g h) := by
  exact mapDesc_property_of_diagonal f g h _ (relativelyRepresentable_diagonal h)

/-- The canonical fibre-product comparison induced by a morphism of algebraic spaces
is representably locally of finite type. -/
theorem locallyOfFiniteType_mapDesc {S : Scheme.{u}} {X Y Z T : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (MorphismProperty.over (@AlgebraicGeometry.LocallyOfFiniteType :
        MorphismProperty Scheme.{u})).presheaf (pullback.mapDesc f g h) := by
  letI := MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.over (@AlgebraicGeometry.LocallyOfFiniteType :
      MorphismProperty Scheme.{u})) (F := yoneda (C := Over S))
  exact mapDesc_property_of_diagonal f g h _ (locallyOfFiniteType_diagonal h)

/-- The canonical fibre-product comparison induced by a morphism of algebraic spaces
is representably locally of finite type and locally quasi-finite. -/
theorem locallyQuasiFinite_mapDesc {S : Scheme.{u}} {X Y Z T : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (MorphismProperty.over (@AlgebraicGeometry.LocallyOfFiniteType ⊓
      @AlgebraicGeometry.LocallyQuasiFinite : MorphismProperty Scheme.{u})).presheaf
      (pullback.mapDesc f g h) := by
  letI := MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.over (@AlgebraicGeometry.LocallyOfFiniteType ⊓
      @AlgebraicGeometry.LocallyQuasiFinite : MorphismProperty Scheme.{u})) (F := yoneda (C := Over S))
  exact mapDesc_property_of_diagonal f g h _ (locallyQuasiFinite_diagonal h)

/-- The canonical fibre-product comparison induced by a morphism of algebraic spaces
is representably separated. -/
theorem isSeparated_mapDesc {S : Scheme.{u}} {X Y Z T : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (MorphismProperty.over (@AlgebraicGeometry.IsSeparated :
        MorphismProperty Scheme.{u})).presheaf (pullback.mapDesc f g h) := by
  letI := MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.over (@AlgebraicGeometry.IsSeparated :
      MorphismProperty Scheme.{u})) (F := yoneda (C := Over S))
  exact mapDesc_property_of_diagonal f g h _ (isSeparated_diagonal h)

/-- The canonical fibre-product comparison induced by a morphism of algebraic spaces
is representably a monomorphism. -/
theorem monomorphisms_mapDesc {S : Scheme.{u}} {X Y Z T : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (MorphismProperty.over (MorphismProperty.monomorphisms Scheme.{u})).presheaf
      (pullback.mapDesc f g h) := by
  letI := MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.over (MorphismProperty.monomorphisms Scheme.{u})) (F := yoneda (C := Over S))
  exact mapDesc_property_of_diagonal f g h _ (monomorphisms_diagonal h)

/-- The canonical fibre-product comparison induced by a locally separated morphism
of algebraic spaces is an immersion. -/
instance isImmersion_mapDesc {S : Scheme.{u}} {X Y Z T : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) [LocallySeparated h] :
    IsImmersion (pullback.mapDesc f g h) := by
  letI := MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.over (@AlgebraicGeometry.IsImmersion :
      MorphismProperty Scheme.{u})) (F := yoneda (C := Over S))
  exact ⟨mapDesc_property_of_diagonal f g h _
    (LocallySeparated.isImmersion_diagonal (f := h))⟩

/-- The canonical fibre-product comparison induced by a separated morphism of
algebraic spaces is a closed immersion. -/
instance isClosedImmersion_mapDesc {S : Scheme.{u}} {X Y Z T : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) [Separated h] :
    IsClosedImmersion (pullback.mapDesc f g h) := by
  letI := MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.over (@AlgebraicGeometry.IsClosedImmersion :
      MorphismProperty Scheme.{u})) (F := yoneda (C := Over S))
  exact ⟨mapDesc_property_of_diagonal f g h _
    (inferInstance : Separated h).isClosedImmersion_diagonal⟩

/-- The canonical fibre-product comparison induced by a quasi-separated morphism
of algebraic spaces is representably quasi-compact. -/
theorem quasiCompact_mapDesc {S : Scheme.{u}} {X Y Z T : AlgebraicSpace S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) [QuasiSeparated h] :
    (MorphismProperty.over (@AlgebraicGeometry.QuasiCompact :
        MorphismProperty Scheme.{u})).presheaf (pullback.mapDesc f g h) := by
  letI := MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.over (@AlgebraicGeometry.QuasiCompact :
      MorphismProperty Scheme.{u})) (F := yoneda (C := Over S))
  exact mapDesc_property_of_diagonal f g h _
    (inferInstance : QuasiSeparated h).quasiCompact_diagonal

end AlgebraicGeometry.AlgebraicSpace
