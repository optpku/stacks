/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Pushout.Gluing

/-!
# Morphism properties of pushout gluing

Morphisms from schemes obtained by pushout gluing have the standard local
morphism properties exactly when both component morphisms do.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Pushout.Gluing

variable {X X' Y : Scheme.{u}}
variable (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [IsAffineHom f]

/-- A scheme obtained by pushout gluing is locally of finite type over `pushout i f`
exactly when both components are locally of finite type. -/
theorem locallyOfFiniteType_iff
    (P : CategoricalPullback (Over.pullback f) (Over.pullback i)) :
    LocallyOfFiniteType ((Gluing.glue i f).obj P).hom ↔
      LocallyOfFiniteType P.fst.hom ∧ LocallyOfFiniteType P.snd.hom := sorry

/-- A scheme obtained by pushout gluing is flat over `pushout i f` exactly when both
components are flat. -/
theorem flat_iff (P : CategoricalPullback (Over.pullback f) (Over.pullback i)) :
    AlgebraicGeometry.Flat ((Gluing.glue i f).obj P).hom ↔
      AlgebraicGeometry.Flat P.fst.hom ∧ AlgebraicGeometry.Flat P.snd.hom := sorry

/-- A scheme obtained by pushout gluing is flat and locally of finite presentation exactly
when both components have these two properties. -/
theorem flatLocallyOfFinitePresentation_iff
    (P : CategoricalPullback (Over.pullback f) (Over.pullback i)) :
    (AlgebraicGeometry.Flat ((Gluing.glue i f).obj P).hom ∧
        LocallyOfFinitePresentation ((Gluing.glue i f).obj P).hom) ↔
      (AlgebraicGeometry.Flat P.fst.hom ∧ LocallyOfFinitePresentation P.fst.hom) ∧
        (AlgebraicGeometry.Flat P.snd.hom ∧ LocallyOfFinitePresentation P.snd.hom) := sorry

/-- A scheme obtained by pushout gluing is smooth over `pushout i f` exactly when both
components are smooth. -/
theorem smooth_iff (P : CategoricalPullback (Over.pullback f) (Over.pullback i)) :
    Smooth ((Gluing.glue i f).obj P).hom ↔ Smooth P.fst.hom ∧ Smooth P.snd.hom := sorry

/-- A scheme obtained by pushout gluing is étale over `pushout i f` exactly when both
components are étale. -/
theorem etale_iff (P : CategoricalPullback (Over.pullback f) (Over.pullback i)) :
    Etale ((Gluing.glue i f).obj P).hom ↔ Etale P.fst.hom ∧ Etale P.snd.hom := sorry

end AlgebraicGeometry.Scheme.Pushout.Gluing
