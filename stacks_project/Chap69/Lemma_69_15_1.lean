/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap69.Lemma_69_15_1_Generation
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Lemma 69.15.1: let `S` be a scheme. Let `X` be a Noetherian algebraic space over `S`.
Every quasi-coherent `𝒪_X`-module is the filtered colimit of its coherent submodules. -/
@[stacks 07UV] #check
  (coherentSubobjects_isDirectedColimit :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
      (F : X.Modules) [F.IsQuasicoherent],
      DirectedOn (· ≤ ·) (coherentSubobjects F) ∧
        IsLUB (coherentSubobjects F) (⊤ : Subobject F))
