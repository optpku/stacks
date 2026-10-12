/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap70.Lemma_70_9_2_Generation
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Lemma 70.9.2: let `S` be a scheme. Let `X` be a quasi-compact and quasi-separated algebraic
space over `S`. Let `F` be a quasi-coherent `𝒪_X`-module. Then `F` is the directed colimit of
its finite type quasi-coherent submodules. -/
@[stacks 0829] #check
  (finiteTypeQuasiCoherentSubobjects_isDirectedColimit :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsQuasiCompact X]
      [IsAbsolutelyQuasiSeparated X] (F : X.Modules) [F.IsQuasicoherent],
      DirectedOn (· ≤ ·) (finiteTypeQuasiCoherentSubobjects F) ∧
        IsLUB (finiteTypeQuasiCoherentSubobjects F) (⊤ : Subobject F))
