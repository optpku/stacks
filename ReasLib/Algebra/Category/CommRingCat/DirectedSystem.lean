/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.CategoryTheory.Category.Preorder

@[expose] public section

universe u v

open CategoryTheory

namespace CommRingCat

/-- Transition morphisms between a preorder-indexed family of commutative rings are
compatible when successive transitions compose to the corresponding direct transition,
without requiring self-transitions to be identities. -/
def IsCompatibleSystem {I : Type u} [Preorder I] (rings : I → CommRingCat.{v})
    (transition : ∀ {i j : I}, i ≤ j → (rings i ⟶ rings j)) : Prop :=
  ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k),
    transition hij ≫ transition hjk = transition (hij.trans hjk)

/-- Compatibility of transition morphisms is equivalent to compatibility of their
successive evaluations on every ring element. -/
theorem isCompatibleSystem_iff {I : Type u} [Preorder I] (rings : I → CommRingCat.{v})
    (transition : ∀ {i j : I}, i ≤ j → (rings i ⟶ rings j)) :
    IsCompatibleSystem rings transition ↔
      ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (element : rings i),
        transition hjk (transition hij element) = transition (hij.trans hjk) element := sorry

/-- A functor from a preorder to commutative rings supplies compatible transition
morphisms. -/
theorem isCompatibleSystem_of_functor {I : Type u} [Preorder I]
    (diagram : I ⥤ CommRingCat.{v}) :
    IsCompatibleSystem diagram.obj
      (fun {_ _} inequality => diagram.map (homOfLE inequality)) := sorry

/-- The colimit of a composition-compatible system of commutative rings over a nonempty
directed preorder is the bundled ring given by `Ring.DirectLimit`. -/
noncomputable def directLimit {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (rings : I → CommRingCat.{v})
    (transition : ∀ {i j : I}, i ≤ j → (rings i ⟶ rings j))
    (compatibility : CommRingCat.IsCompatibleSystem rings transition) : CommRingCat.{max u v} :=
  CommRingCat.of (Ring.DirectLimit (fun i => rings i) (fun _ _ inequality => transition inequality))

end CommRingCat
