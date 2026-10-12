/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap70.Lemma_70_9_5_FiniteTypeGeneration
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder

universe u

/- Lemma 70.9.5: let `S` be a scheme. Let `X` be a quasi-compact and quasi-separated algebraic
space over `S`. Let `𝒜` be a quasi-coherent `𝒪_X`-algebra. Then `𝒜` is the directed colimit of
its finite type quasi-coherent `𝒪_X`-subalgebras. -/
@[stacks 082B] #check
  (finiteTypeQuasiCoherentSubalgebras_isDirectedColimit :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsQuasiCompact X]
      [IsAbsolutelyQuasiSeparated X] (A : X.QcAlgebraUnder),
      DirectedOn (· ≤ ·) (finiteTypeQuasiCoherentSubalgebras A) ∧
        IsLUB (finiteTypeQuasiCoherentSubalgebras A) (⊤ : Subobject A.obj))
