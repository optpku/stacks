/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Algebra.Integral
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder

universe u

/- Lemma 70.9.7 (1): let `S` be a scheme. Let `X` be a quasi-compact and quasi-separated
algebraic space over `S`. Let `A` be an integral quasi-coherent `𝒪_X`-algebra. Then `A` is
the directed colimit of its finite quasi-coherent `𝒪_X`-subalgebras. -/
@[stacks 082C] #check
  (AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.finiteQuasiCoherentSubalgebras_directedColimit_of_isIntegral :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsQuasiCompact X]
      [IsAbsolutelyQuasiSeparated X] (A : X.QcAlgebraUnder) [IsIntegral A],
      (finiteQuasiCoherentSubalgebras A).Nonempty ∧
        DirectedOn (· ≤ ·) (finiteQuasiCoherentSubalgebras A) ∧
          (∀ c : CategoryTheory.Limits.Cocone (finiteSubalgebraDiagram A),
            ∃! f : A.obj ⟶ c.pt, ∀ B : finiteQuasiCoherentSubalgebras A,
              B.val.arrow ≫ f = c.ι.app B))

/- Lemma 70.9.7 (2): let `S` be a scheme. Let `X` be a quasi-compact and quasi-separated
algebraic space over `S`. Let `A` be an integral quasi-coherent `𝒪_X`-algebra. Then `A` is
a directed colimit of finite and finitely presented `𝒪_X`-algebras. -/
@[stacks 082C] #check
  (AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.finiteFinitelyPresentable_ind_of_isIntegral :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsQuasiCompact X]
      [IsAbsolutelyQuasiSeparated X] (A : X.QcAlgebraUnder) [IsIntegral A],
      ObjectProperty.ind.{u}
        (fun B : Under (commStructureSheaf X) ↦
          finiteProperty X B ∧ finitelyPresentableProperty X B) A.obj)
