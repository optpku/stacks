/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Transitivity
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Presentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Glueing

/-!
# Étale-local splittings of conormal transitivity sequences

This file records the proposition that the canonical conormal transitivity
complex is short exact and splits after pullback along an étale covering family.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.Transitivity

variable {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}

/-- The canonical conormal transitivity complex is short exact and étale-locally split. -/
def IsShortExactLocallySplit (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [IsImmersion j] : Prop :=
  (complex i j).ShortExact ∧
    ∃ (I : Type u) (U : I → smallEtaleSite Z),
      (smallEtaleTopology Z).CoversTop U ∧
        ∀ k : I, Nonempty (((complex i j).map (Modules.pullback (U k).hom)).Splitting)

/-- The defining characterization of étale-local splitting. -/
theorem isShortExactLocallySplit_iff (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [IsImmersion j] :
    IsShortExactLocallySplit i j ↔
      (complex i j).ShortExact ∧
        ∃ (I : Type u) (U : I → smallEtaleSite Z),
          (smallEtaleTopology Z).CoversTop U ∧
            ∀ k : I,
              Nonempty (((complex i j).map (Modules.pullback (U k).hom)).Splitting) :=
  Iff.rfl

/-- The short exactness and covering-family data provided by local splitting. -/
theorem IsShortExactLocallySplit.spec (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [IsImmersion j] (h : IsShortExactLocallySplit i j) :
    (complex i j).ShortExact ∧
      ∃ (I : Type u) (U : I → smallEtaleSite Z),
        (smallEtaleTopology Z).CoversTop U ∧
          ∀ k : I, Nonempty (((complex i j).map (Modules.pullback (U k).hom)).Splitting) :=
  h

end AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.Transitivity
