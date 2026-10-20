/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Algebra.FiniteTypeGeneration
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 70.9.5: let `S` be a scheme. Let `X` be a quasi-compact and quasi-separated algebraic
space over `S`. Let `𝒜` be a quasi-coherent `𝒪_X`-algebra. Then `𝒜` is the directed colimit of
its finite type quasi-coherent `𝒪_X`-subalgebras. -/
@[stacks 082B] #check
  (AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.finiteTypeQuasiCoherentSubalgebras_directedColimit :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsQuasiCompact X]
      [IsAbsolutelyQuasiSeparated X] (A : X.QcAlgebraUnder),
      (AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.finiteTypeQuasiCoherentSubalgebras A).Nonempty ∧
        DirectedOn (· ≤ ·)
          (AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.finiteTypeQuasiCoherentSubalgebras A) ∧
          (∀ c : CategoryTheory.Limits.Cocone
            (AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.finiteTypeSubalgebraDiagram A),
            ∃! f : A.obj ⟶ c.pt,
              ∀ B : AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.finiteTypeQuasiCoherentSubalgebras A,
                B.val.arrow ≫ f = c.ι.app B))
