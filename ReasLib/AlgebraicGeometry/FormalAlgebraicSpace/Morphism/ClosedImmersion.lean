/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fppf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fpqc.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion.Fpqc
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Property.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Pullback
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Basic

/-!
# Closed immersions of presheaves over a scheme

A morphism of presheaves over a scheme is a closed immersion when it is
representable by algebraic spaces and every scheme Yoneda pullback is a closed
immersion of algebraic spaces. This property is stable under arbitrary base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- A morphism of functors of points on schemes over `S` is a closed
immersion when it is representable by algebraic spaces and every Yoneda
pullback is a closed immersion of algebraic spaces. -/
@[mk_iff]
class ClosedImmersion {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) :
    Prop where
  /-- `f` is representable by algebraic spaces. -/
  representable : representableByAlgebraicSpaces f
  /-- Every Yoneda pullback of `f` is a closed immersion of algebraic spaces. -/
  of_pullback :
    ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
      AlgebraicSpace.IsClosedImmersion (representableByAlgebraicSpaces.pullbackHom representable ξ)

private theorem isAlgebraicSpace_of_yoneda_iso {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} {U : Over S} (e : F ≅ yoneda.obj U) :
    AlgebraicSpace.IsAlgebraicSpace F := by
  refine ⟨(Presheaf.isSheaf_of_iso_iff e).mpr (AlgebraicSpace.ofOver_isSheaf U), ?_,
    ⟨U, e.inv, ?_, inferInstance⟩⟩
  · apply Functor.relativelyRepresentable.diag_of_map_from_obj
    intro V f
    have hf : yoneda.relativelyRepresentable (f ≫ e.hom) := by
      rw [← yoneda.map_preimage (f ≫ e.hom)]
      exact Functor.relativelyRepresentable.map _ _
    simpa using MorphismProperty.comp_mem _ _ _ hf
      (Functor.relativelyRepresentable.of_isIso yoneda e.inv)
  · refine ⟨Functor.relativelyRepresentable.of_isIso yoneda _, ?_⟩
    intro a b g fst snd h
    have : IsIso (yoneda.map snd) := h.isIso_snd_of_isIso
    have : IsIso snd := isIso_of_reflects_iso snd yoneda
    have : IsIso snd.left := inferInstanceAs (IsIso ((Over.forget S).map snd))
    change AlgebraicGeometry.Etale snd.left
    infer_instance

namespace ClosedImmersion

/-- A morphism of functors of points is a closed immersion if and only if it is
representable by algebraic spaces and every Yoneda pullback is a closed
immersion of algebraic spaces. -/
theorem iff {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) :
    ClosedImmersion f ↔
      ∃ (h : representableByAlgebraicSpaces f),
        ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
          AlgebraicSpace.IsClosedImmersion (representableByAlgebraicSpaces.pullbackHom h ξ) := by
  constructor
  · intro h
    exact ⟨h.representable, h.of_pullback⟩
  · rintro ⟨h, hP⟩
    exact ⟨h, hP⟩

/-- The identity morphism of a functor of points is a closed immersion. -/
instance id {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u} : ClosedImmersion (𝟙 X) := by
  have h : representableByAlgebraicSpaces (𝟙 X) := by
    intro U ξ
    haveI : IsIso (pullback.fst ξ (𝟙 X)) :=
      (IsPullback.of_hasPullback ξ (𝟙 X)).isIso_fst_of_isIso
    exact isAlgebraicSpace_of_yoneda_iso (asIso (pullback.fst ξ (𝟙 X)))
  have hrel : AlgebraicSpace.relativeAlgebraicSpaces
      (@AlgebraicSpace.IsClosedImmersion S) (𝟙 X) := by
    apply AlgebraicSpace.relativeAlgebraicSpaces.of _ h
    intro U ξ
    rw [representableByAlgebraicSpaces.pullbackHom_fst]
    haveI : IsIso (pullback.fst ξ (𝟙 X)) :=
      (IsPullback.of_hasPullback ξ (𝟙 X)).isIso_fst_of_isIso
    apply AlgebraicSpace.isClosedImmersion_iff _ |>.2
    change (MorphismProperty.over (@AlgebraicGeometry.IsClosedImmersion :
      MorphismProperty Scheme.{u})).relative yoneda (pullback.fst ξ (𝟙 X))
    refine ⟨Functor.relativelyRepresentable.of_isIso yoneda _, ?_⟩
    intro a b g fst snd hsq
    have : IsIso (yoneda.map snd) := hsq.isIso_snd_of_isIso
    have : IsIso snd := isIso_of_reflects_iso snd yoneda
    have : IsIso snd.left := inferInstanceAs (IsIso ((Over.forget S).map snd))
    change AlgebraicGeometry.IsClosedImmersion snd.left
    infer_instance
  exact ⟨hrel.1, hrel.2 hrel.1⟩

/-- The composite of two closed immersions of presheaves over a scheme is a closed
immersion of formal algebraic spaces. -/
@[stacks 0GHW]
instance comp {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace Z]
    [ClosedImmersion f] [ClosedImmersion g] :
    ClosedImmersion (f ≫ g) := by
  have hf : ClosedImmersion f := inferInstance
  have hg : ClosedImmersion g := inferInstance
  have hfg : AlgebraicSpace.relativeAlgebraicSpaces
      (@AlgebraicSpace.IsClosedImmersion S) f :=
    AlgebraicSpace.relativeAlgebraicSpaces.of _ hf.representable hf.of_pullback
  have hgg : AlgebraicSpace.relativeAlgebraicSpaces
      (@AlgebraicSpace.IsClosedImmersion S) g :=
    AlgebraicSpace.relativeAlgebraicSpaces.of _ hg.representable hg.of_pullback
  letI : MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.IsClosedImmersion S)
      (AlgebraicSpace.fppfPrecoverage S) :=
    MorphismProperty.IsLocalAtTarget.of_le (by
      intro F R hR
      obtain ⟨ι, Fᵢ, k, rfl⟩ := R.exists_eq_ofArrows
      exact (AlgebraicSpace.ofArrows_mem_fpqcPrecoverage_iff k).mpr
        (AlgebraicSpace.fpqcCovering_of_fppfCovering
          ((AlgebraicSpace.fppfCovering_iff_mem_precoverage Fᵢ k).mpr hR)))
  have hcomp := AlgebraicSpace.relativeAlgebraicSpaces.comp f g hfg hgg
  exact ⟨hcomp.1, hcomp.2 hcomp.1⟩

/-- A closed immersion is representable by algebraic spaces. -/
theorem relativelyRepresentable {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) [ClosedImmersion f] : representableByAlgebraicSpaces f := by
  let h : ClosedImmersion f := inferInstance
  exact h.representable

/-- Yoneda pullbacks of a closed immersion are closed immersions of algebraic
spaces. -/
theorem spec {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    [hf : ClosedImmersion f] {U : Over S} (ξ : yoneda.obj U ⟶ Y) :
    representableByAlgebraicSpaces f ∧
      AlgebraicSpace.IsClosedImmersion (representableByAlgebraicSpaces.pullbackHom hf.representable ξ) := by
  exact ⟨hf.representable, hf.of_pullback ξ⟩

end ClosedImmersion

/-- In a pullback square of presheaves over a scheme, the base change of a
closed immersion is a closed immersion. -/
theorem closedImmersion_of_isPullback {S : Scheme.{u}}
    {X Y Y' B : (Over S)ᵒᵖ ⥤ Type u}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : ClosedImmersion g) :
    ClosedImmersion g' := by
  have hg' : AlgebraicSpace.relativeAlgebraicSpaces
      (@AlgebraicSpace.IsClosedImmersion S) g :=
    AlgebraicSpace.relativeAlgebraicSpaces.of _ hg.representable hg.of_pullback
  have hbase := AlgebraicSpace.relativeAlgebraicSpaces.of_isPullback sq hg'
  exact ⟨hbase.1, hbase.2 hbase.1⟩

/-- The base-change projection `pullback.snd f g` of a closed immersion
`f : X ⟶ Y` of presheaves over a scheme is a closed immersion. -/
instance closedImmersion_pullback_snd {S : Scheme.{u}}
    {X Y Z : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (g : Z ⟶ Y)
    [HasPullback f g] [ClosedImmersion f] : ClosedImmersion (pullback.snd f g) := by
  exact closedImmersion_of_isPullback (IsPullback.of_hasPullback f g)
    (inferInstance : ClosedImmersion f)

end AlgebraicGeometry.FormalAlgebraicSpace
