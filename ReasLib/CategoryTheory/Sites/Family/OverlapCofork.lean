/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Augmentation
public import ReasLib.CategoryTheory.Limits.ChosenPullback.Canonical

/-!
# Overlap coforks of fixed-target families

Formal coproducts of arrows to a fixed target have a pairwise-overlap family, two projection
maps, and an augmented cofork of representable presheaves, independently of any topology.
-/

@[expose] public section

noncomputable section

universe w v u v' u'

namespace CategoryTheory

open Limits Opposite

namespace Limits.FormalCoproduct

variable {D : Type u} [Category.{v} D] {V : D}

/-- The chosen pullback of two structure arrows in a fixed-target formal coproduct. -/
noncomputable def chosenOverlap (K : FormalCoproduct.{w} (CategoryTheory.Over V))
    [K.toPresieve.HasPairwisePullbacks] (i j : K.I) :
    ChosenPullback (K.obj i).hom (K.obj j).hom :=
  ChosenPullback.ofHasPullbackProof
    (Presieve.HasPairwisePullbacks.has_pullbacks (R := K.toPresieve)
      (Presieve.ofArrows.mk i) (Presieve.ofArrows.mk j))

/-- The family of pairwise overlaps of the members of `K`, indexed by ordered pairs. -/
noncomputable def overlapFamily (K : FormalCoproduct.{w} (CategoryTheory.Over V))
    [K.toPresieve.HasPairwisePullbacks] : FormalCoproduct.{w} (CategoryTheory.Over V) :=
  ofArrows
    (fun ij : K.I × K.I ↦ (chosenOverlap K ij.1 ij.2).pullback)
    (fun ij ↦ (chosenOverlap K ij.1 ij.2).p)

/-- The first overlap projection lies over the common target. -/
theorem overlapFst_hom (K : FormalCoproduct.{w} (CategoryTheory.Over V))
    [K.toPresieve.HasPairwisePullbacks] (i j : K.I) :
    (chosenOverlap K i j).p₁ ≫ (K.obj i).hom =
      ((overlapFamily K).obj (i, j)).hom := sorry

/-- The second overlap projection lies over the common target. -/
theorem overlapSnd_hom (K : FormalCoproduct.{w} (CategoryTheory.Over V))
    [K.toPresieve.HasPairwisePullbacks] (i j : K.I) :
    (chosenOverlap K i j).p₂ ≫ (K.obj j).hom =
      ((overlapFamily K).obj (i, j)).hom := sorry

/-- The first projection from the pairwise-overlap family to the original family. -/
noncomputable def overlapFst (K : FormalCoproduct.{w} (CategoryTheory.Over V))
    [K.toPresieve.HasPairwisePullbacks] : overlapFamily K ⟶ K where
  f := fun ij ↦ ij.1
  φ := fun ij ↦ CategoryTheory.Over.homMk
    (chosenOverlap K ij.1 ij.2).p₁ (overlapFst_hom K ij.1 ij.2)

/-- The second projection from the pairwise-overlap family to the original family. -/
noncomputable def overlapSnd (K : FormalCoproduct.{w} (CategoryTheory.Over V))
    [K.toPresieve.HasPairwisePullbacks] : overlapFamily K ⟶ K where
  f := fun ij ↦ ij.2
  φ := fun ij ↦ CategoryTheory.Over.homMk
    (chosenOverlap K ij.1 ij.2).p₂ (overlapSnd_hom K ij.1 ij.2)

/-- The two overlap maps agree after the canonical augmentation to the fixed target. -/
theorem overlap_augmentation_parallel (K : FormalCoproduct.{w} (CategoryTheory.Over V))
    [K.toPresieve.HasPairwisePullbacks] :
    toPresheaf.map ((forgetOver V).map (overlapFst K)) ≫ augmentation K =
      toPresheaf.map ((forgetOver V).map (overlapSnd K)) ≫ augmentation K := sorry

/-- The canonical cofork from pairwise overlap representables to the representable presheaf of
the fixed target. -/
noncomputable def overlapCofork (K : FormalCoproduct.{w} (CategoryTheory.Over V))
    [K.toPresieve.HasPairwisePullbacks] :
    Cofork (toPresheaf.map ((forgetOver V).map (overlapFst K)))
      (toPresheaf.map ((forgetOver V).map (overlapSnd K))) :=
  Cofork.ofπ (augmentation K) (overlap_augmentation_parallel K)

variable {C : Type u'} [Category.{v'} C]

/-- Whiskering the overlap maps along a functor preserves their common augmentation. -/
theorem whiskerLeft_overlap_augmentation_parallel (u : C ⥤ D)
    (K : FormalCoproduct.{w} (CategoryTheory.Over V)) [K.toPresieve.HasPairwisePullbacks] :
    u.op.whiskerLeft (toPresheaf.map ((forgetOver V).map (overlapFst K))) ≫
        u.op.whiskerLeft (augmentation K) =
      u.op.whiskerLeft (toPresheaf.map ((forgetOver V).map (overlapSnd K))) ≫
        u.op.whiskerLeft (augmentation K) := sorry

/-- Restricting the overlap presentation of a fixed-target family along `u` gives the canonical
cofork from pairwise-overlap representables to the representable
presheaf of the fixed target. -/
@[stacks 00XK]
noncomputable def whiskerLeftOverlapCofork (u : C ⥤ D)
    (K : FormalCoproduct.{w} (CategoryTheory.Over V)) [K.toPresieve.HasPairwisePullbacks] :
    Cofork
      (u.op.whiskerLeft (toPresheaf.map ((forgetOver V).map (overlapFst K))))
      (u.op.whiskerLeft (toPresheaf.map ((forgetOver V).map (overlapSnd K)))) :=
  Cofork.ofπ (u.op.whiskerLeft (augmentation K))
    (whiskerLeft_overlap_augmentation_parallel u K)

end Limits.FormalCoproduct

end CategoryTheory
