/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.WeaklyContractible.Enough
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] (K : Coverage C)

/- Definition 7.40.2 (1): an object U of a site C is weakly contractible if the
equivalent conditions of Lemma 7.40.1 hold. -/
@[stacks 090L "(1)"]
#check (CategoryTheory.GrothendieckTopology.IsWeaklyContractible K.toGrothendieck : C → Prop)

/- Definition 7.40.2 (2): a site has enough weakly contractible objects if every
object U of C has a covering {Uᵢ ⟶ U} with Uᵢ weakly contractible for all i. -/
@[stacks 090L "(2)"]
#check (CategoryTheory.Coverage.HasEnoughObjectsWithProperty K
  K.toGrothendieck.IsWeaklyContractible : Prop)

#check (CategoryTheory.Coverage.HasEnoughObjectsWithProperty.iff_existsWeaklyContractibleCover K :
  K.HasEnoughObjectsWithProperty K.toGrothendieck.IsWeaklyContractible ↔
    ∀ U : C, ∃ families : Limits.FormalCoproduct.{max u v} (CategoryTheory.Over U),
      Presieve.ofArrows (fun i => (families.obj i).left) (fun i => (families.obj i).hom) ∈ K U ∧
        ∀ i : families.index, K.toGrothendieck.IsWeaklyContractible (families.obj i).left)

/- Definition 7.40.2 (3): more generally, if P is a property of objects of C, the
site has enough P-objects if every object U of C has a covering {Uᵢ ⟶ U} such
that Uᵢ has P for all i. -/
@[stacks 090L "(3)"]
#check (CategoryTheory.Coverage.HasEnoughObjectsWithProperty K : ObjectProperty C → Prop)

variable (P : ObjectProperty C)

#check (CategoryTheory.Coverage.HasEnoughObjectsWithProperty.iff_existsCoveringFamily K P :
  K.HasEnoughObjectsWithProperty P ↔
    ∀ U : C, ∃ families : Limits.FormalCoproduct.{max u v} (CategoryTheory.Over U),
      Presieve.ofArrows (fun i => (families.obj i).left) (fun i => (families.obj i).hom) ∈ K U ∧
        ∀ i : families.index, P (families.obj i).left)

#check (CategoryTheory.GrothendieckTopology.HasEnoughObjectsWithProperty.iff_existsWeaklyContractibleCover
  K.toGrothendieck :
  K.toGrothendieck.HasEnoughObjectsWithProperty K.toGrothendieck.IsWeaklyContractible ↔
    ∀ U : C, ∃ families : Limits.FormalCoproduct.{max u v} (CategoryTheory.Over U),
      Sieve.ofArrows (fun i => (families.obj i).left) (fun i => (families.obj i).hom) ∈
        K.toGrothendieck U ∧
          ∀ i : families.index, K.toGrothendieck.IsWeaklyContractible (families.obj i).left)
