/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap103.Lemma_103_18_1_Generation
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicStack
open GroupoidsOver

universe u

/- Lemma 103.18.1: let `X` be a Noetherian algebraic stack.
Every quasi-coherent `𝒪_X`-module is the filtered colimit of its coherent submodules. -/
@[stacks 0GRF] #check
  (coherentSubobjects_isDirectedColimit :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] [IsNoetherian X]
      (F : SheafOfModules.{u} (structureSheaf X)) [F.IsQuasicoherent],
      DirectedOn (· ≤ ·) (coherentSubobjects F) ∧
        IsLUB (coherentSubobjects F) (⊤ : Subobject F))
