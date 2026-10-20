/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Pointwise Homology of Short Complexes in Functor Categories

This file identifies the homology of a short complex in a functor category with the diagram
obtained by taking homology pointwise. The construction is independent of whether the diagram
will subsequently be used with a limit or a colimit.
-/

@[expose] public section

universe v u v' u'

open CategoryTheory

noncomputable section

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {J : Type u'} [Category.{v'} J]

namespace DiagramHomology

/-- The canonical pointwise comparison between homology in a functor category and homology of
the corresponding short complex at one diagram index. -/
noncomputable def componentIso (S : ShortComplex (J ⥤ C)) (j : J) :
    S.homology.obj j ≅
      (((functorEquivalence J C).functor.obj S).obj j).homology :=
  (S.mapHomologyIso ((evaluation J C).obj j)).symm

namespace componentIso

/-- The pointwise homology comparisons are natural in the diagram index. -/
theorem naturality (S : ShortComplex (J ⥤ C)) {i j : J} (f : i ⟶ j) :
    S.homology.map f ≫ (componentIso S j).hom =
      (componentIso S i).hom ≫
        (homologyFunctor C).map (((functorEquivalence J C).functor.obj S).map f) := sorry

end componentIso

/-- Homology in the functor category is canonically the pointwise homology diagram. -/
noncomputable def diagramIso (S : ShortComplex (J ⥤ C)) :
    S.homology ≅
      (functorEquivalence J C).functor.obj S ⋙ homologyFunctor C :=
  NatIso.ofComponents (componentIso S) (componentIso.naturality S)

/-- For a diagram of short complexes, the homology of its owner under `functorEquivalence` is
canonically the original diagram followed by `homologyFunctor C`. -/
noncomputable def comparisonIso (S : J ⥤ ShortComplex C) :
    ((functorEquivalence J C).inverse.obj S).homology ≅ S ⋙ homologyFunctor C :=
  diagramIso ((functorEquivalence J C).inverse.obj S) ≪≫
    Functor.isoWhiskerRight
      ((functorEquivalence J C).counitIso.app S) (homologyFunctor C)

end DiagramHomology

end CategoryTheory.ShortComplex
