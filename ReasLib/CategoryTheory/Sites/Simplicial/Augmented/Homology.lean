/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Simplicial.Augmented.LocalHypercover
import Mathlib.Tactic.CrossRefAttribute

/-!
# Homology of augmented simplicial presheaves

This leaf records the local-hypercover hypotheses under which an augmented
simplicial presheaf has the expected homology sheaves.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory

open Limits
open Opposite
open scoped Simplicial

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasSheafify J AddCommGrpCat.{max w v}]
variable {A : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type (max w v))}

namespace SimplicialObject.Augmented.IsLocalHypercover.Homology

/-- Lemma 25.4.4 (1): a local hypercover has vanishing positive-degree homology sheaves. -/
@[stacks 01GE "positive degrees"]
theorem succ_isZero (hA : A.IsLocalHypercover J) (n : ℕ) :
    IsZero ((SimplicialPresheaf.Homology.functor J (n + 1)).obj A.left) := sorry

/-- Lemma 25.4.4 (2): the degree-zero homology of a local hypercover is the free abelian sheaf on
its augmentation target. -/
@[stacks 01GE "degree zero"]
theorem augmentationMap_isIso (hA : A.IsLocalHypercover J) :
    IsIso (SimplicialPresheaf.Homology.augmentationMap J A) := sorry

end SimplicialObject.Augmented.IsLocalHypercover.Homology

end CategoryTheory
