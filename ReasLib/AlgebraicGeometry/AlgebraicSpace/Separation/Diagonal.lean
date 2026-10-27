/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Properties of the diagonal of an algebraic space

The diagonal of an algebraic space is representably locally of finite type,
a monomorphism, separated, and locally quasi-finite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The relative diagonal is the base change of the product diagonal along
`F ×_G F ⟶ F × F`. -/
private theorem diagonal_isPullback_diag {S : Scheme.{u}}
    {F G : (Over S)ᵒᵖ ⥤ Type u} (f : F ⟶ G) :
    IsPullback (𝟙 F) (pullback.diagonal f) (Limits.diag F)
      (prod.lift (pullback.fst f f) (pullback.snd f f)) := by
  haveI : Mono (prod.lift (pullback.fst f f) (pullback.snd f f)) := by
    constructor
    intro W a b h
    apply pullback.hom_ext
    · simpa only [Category.assoc, prod.lift_fst] using
        congrArg (fun k ↦ k ≫ prod.fst) h
    · simpa only [Category.assoc, prod.lift_snd] using
        congrArg (fun k ↦ k ≫ prod.snd) h
  exact IsPullback.of_horiz_isIso_mono ⟨by ext <;> simp⟩

private theorem diagonal_presheaf_of_diag {S : Scheme.{u}}
    {F G : (Over S)ᵒᵖ ⥤ Type u} (f : F ⟶ G) {P : MorphismProperty (Over S)}
    (h : P.presheaf (Limits.diag F)) : P.presheaf (pullback.diagonal f) := by
  letI := MorphismProperty.relative_isStableUnderBaseChange P (F := yoneda)
  exact MorphismProperty.of_isPullback (diagonal_isPullback_diag f) h

/-- The diagonal of an algebraic space over a scheme is representably locally of finite type. -/
@[stacks 02X4]
theorem locallyOfFiniteType_diag {S : Scheme.{u}} (F : AlgebraicSpace S) :
    (MorphismProperty.over (@AlgebraicGeometry.LocallyOfFiniteType :
        MorphismProperty Scheme.{u})).presheaf (diag F) :=
  sorry

/-- The diagonal of an algebraic space over a scheme is representably a monomorphism. -/
@[stacks 02X4]
theorem monomorphisms_diag {S : Scheme.{u}} (F : AlgebraicSpace S) :
    (MorphismProperty.over (MorphismProperty.monomorphisms Scheme.{u})).presheaf (diag F) := by
  refine ⟨F.representableDiagonal, ?_⟩
  intro U V ξ fst snd sq
  haveI : Mono (yoneda.map snd) := sq.mono_snd_of_mono
  haveI : Mono snd := yoneda.mono_of_mono_map inferInstance
  exact inferInstanceAs (Mono snd.left)

/-- The diagonal of an algebraic space over a scheme is representably separated. -/
@[stacks 02X4]
theorem isSeparated_diag {S : Scheme.{u}} (F : AlgebraicSpace S) :
    (MorphismProperty.over (@AlgebraicGeometry.IsSeparated :
        MorphismProperty Scheme.{u})).presheaf (diag F) := by
  refine ⟨F.representableDiagonal, ?_⟩
  intro U V ξ fst snd sq
  haveI : Mono snd.left := (monomorphisms_diag F).property ξ fst snd sq
  exact inferInstanceAs (AlgebraicGeometry.IsSeparated snd.left)

/-- The diagonal of an algebraic space over a scheme is representably locally of finite type
and locally quasi-finite. -/
@[stacks 02X4]
theorem locallyQuasiFinite_diag {S : Scheme.{u}} (F : AlgebraicSpace S) :
    (MorphismProperty.over (@AlgebraicGeometry.LocallyOfFiniteType ⊓
      @AlgebraicGeometry.LocallyQuasiFinite : MorphismProperty Scheme.{u})).presheaf (diag F) := by
  refine ⟨F.representableDiagonal, ?_⟩
  intro U V ξ fst snd sq
  haveI : AlgebraicGeometry.LocallyOfFiniteType snd.left :=
    (locallyOfFiniteType_diag F).property ξ fst snd sq
  haveI : Mono snd.left := (monomorphisms_diag F).property ξ fst snd sq
  exact ⟨inferInstance, inferInstance⟩

/-- The relative diagonal of a morphism of algebraic spaces over a scheme is representable
by schemes. -/
@[stacks 03HK]
theorem relativelyRepresentable_diagonal {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    yoneda.relativelyRepresentable (pullback.diagonal (C := (Over S)ᵒᵖ ⥤ Type u) f) := by
  exact MorphismProperty.of_isPullback (diagonal_isPullback_diag f) X.representableDiagonal

/-- The relative diagonal of a morphism of algebraic spaces over a scheme is representably
locally of finite type. -/
@[stacks 03HK]
theorem locallyOfFiniteType_diagonal {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    (MorphismProperty.over (@AlgebraicGeometry.LocallyOfFiniteType :
        MorphismProperty Scheme.{u})).presheaf
      (pullback.diagonal (C := (Over S)ᵒᵖ ⥤ Type u) f) := by
  exact diagonal_presheaf_of_diag f (locallyOfFiniteType_diag X)

/-- The relative diagonal of a morphism of algebraic spaces over a scheme is representably
a monomorphism. -/
@[stacks 03HK]
theorem monomorphisms_diagonal {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    (MorphismProperty.over (MorphismProperty.monomorphisms Scheme.{u})).presheaf
      (pullback.diagonal (C := (Over S)ᵒᵖ ⥤ Type u) f) := by
  exact diagonal_presheaf_of_diag f (monomorphisms_diag X)

/-- The relative diagonal of a morphism of algebraic spaces over a scheme is representably
separated. -/
@[stacks 03HK]
theorem isSeparated_diagonal {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    (MorphismProperty.over (@AlgebraicGeometry.IsSeparated :
        MorphismProperty Scheme.{u})).presheaf
      (pullback.diagonal (C := (Over S)ᵒᵖ ⥤ Type u) f) := by
  exact diagonal_presheaf_of_diag f (isSeparated_diag X)

/-- The relative diagonal of a morphism of algebraic spaces over a scheme is representably
locally of finite type and locally quasi-finite. -/
@[stacks 03HK]
theorem locallyQuasiFinite_diagonal {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    (MorphismProperty.over (@AlgebraicGeometry.LocallyOfFiniteType ⊓
      @AlgebraicGeometry.LocallyQuasiFinite : MorphismProperty Scheme.{u})).presheaf
      (pullback.diagonal (C := (Over S)ᵒᵖ ⥤ Type u) f) := by
  exact diagonal_presheaf_of_diag f (locallyQuasiFinite_diag X)

/-- The relative diagonal of a separated morphism of algebraic spaces is a closed immersion. -/
instance instIsClosedImmersion_pullbackDiagonal {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f] :
    IsClosedImmersion (pullback.diagonal f) := by
  let sq := ReasLibPullback.isPullback f f
  let e : (pullback f f).functorOfPoints ≅
      pullback (C := (Over S)ᵒᵖ ⥤ Type u) f f :=
    { hom := sq.isoPullback.inv
      inv := sq.isoPullback.hom
      hom_inv_id := sq.isoPullback.inv_hom_id
      inv_hom_id := sq.isoPullback.hom_inv_id }
  letI : IsIso e.hom := e.isIso_hom
  have hfst : e.hom ≫ pullback.fst (C := (Over S)ᵒᵖ ⥤ Type u) f f =
      (pullback.fst f f : pullback f f ⟶ X) :=
    sq.isoPullback_inv_fst
  have hsnd : e.hom ≫ pullback.snd (C := (Over S)ᵒᵖ ⥤ Type u) f f =
      (pullback.snd f f : pullback f f ⟶ X) :=
    sq.isoPullback_inv_snd
  let d : X.functorOfPoints ⟶ (pullback (C := AlgebraicSpace S) f f).functorOfPoints :=
    pullback.diagonal (C := AlgebraicSpace S) f
  have hdiag : d ≫ e.hom =
      pullback.diagonal (C := (Over S)ᵒᵖ ⥤ Type u) f := by
    apply pullback.hom_ext
    · rw [Category.assoc, hfst]
      exact (pullback.diagonal_fst (C := AlgebraicSpace S) f).trans
        (pullback.diagonal_fst (C := (Over S)ᵒᵖ ⥤ Type u) f).symm
    · rw [Category.assoc, hsnd]
      exact (pullback.diagonal_snd (C := AlgebraicSpace S) f).trans
        (pullback.diagonal_snd (C := (Over S)ᵒᵖ ⥤ Type u) f).symm
  constructor
  change (MorphismProperty.over (@AlgebraicGeometry.IsClosedImmersion :
    MorphismProperty Scheme.{u})).presheaf d
  apply (MorphismProperty.cancel_right_of_respectsIso
    (MorphismProperty.over (@AlgebraicGeometry.IsClosedImmersion :
      MorphismProperty Scheme.{u})).presheaf d e.hom).mp
  rw [hdiag]
  exact (inferInstance : Separated f).isClosedImmersion_diagonal

end AlgebraicGeometry.AlgebraicSpace
