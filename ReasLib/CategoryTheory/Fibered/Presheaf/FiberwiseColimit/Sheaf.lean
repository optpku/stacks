/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Presheaf.FiberwiseColimit.Adjunction
public import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.Tactic.CrossRefAttribute

/-!
# Sheafified fiberwise colimits

This leaf sheafifies the topology-independent fiberwise-colimit presheaf.  The source topology is
arbitrary: only the underlying source presheaf and the target sheafification are used.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v wX vX a b

namespace CategoryTheory.FiberedCategoryOver.Presheaf.fiberwiseColimit

variable {C : Type u} [Category.{v} C]
variable (X : FiberedCategoryOver.{u, v, wX, vX} C)
variable (A : Type a) [Category.{b} A]
variable (K : GrothendieckTopology X.total) (J : GrothendieckTopology C)
variable [∀ V : C, HasColimitsOfShape (X.p.Fiber V)ᵒᵖ A]
variable [HasWeakSheafify J A]

/-- Fiberwise colimit followed by sheafification, functorially in source sheaves. -/
@[stacks 08PE "sheafified fiberwise colimit functor"]
noncomputable abbrev sheafFunctor : Sheaf K A ⥤ Sheaf J A :=
  sheafToPresheaf K A ⋙ functor X A ⋙ presheafToSheaf J A

/-- The sheafified fiberwise colimit of a source sheaf. -/
@[stacks 08PE "sheafified fiberwise colimit"]
noncomputable abbrev sheaf (F : Sheaf K A) : Sheaf J A :=
  (sheafFunctor X A K J).obj F

/-- Evaluation of the sheafified fiberwise-colimit functor on objects. -/
@[simp, stacks 08PE "sheafified fiberwise colimit object formula"]
theorem sheafFunctor_obj (F : Sheaf K A) :
    (sheafFunctor X A K J).obj F = sheaf X A K J F := sorry

/-- Evaluation of the sheafified fiberwise-colimit functor on morphisms. -/
@[simp, stacks 08PE "sheafified fiberwise colimit map formula"]
theorem sheafFunctor_map {F G : Sheaf K A} (τ : F ⟶ G) :
    (sheafFunctor X A K J).map τ =
      (presheafToSheaf J A).map
        (map X A ((sheafToPresheaf K A).map τ)) := sorry

end CategoryTheory.FiberedCategoryOver.Presheaf.fiberwiseColimit
