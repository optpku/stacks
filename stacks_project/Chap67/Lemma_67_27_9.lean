/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_27_6_LocallyQuasiFinite

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.27.9: If `S` is a scheme and `f : X ⟶ Y` is a finite-type morphism
of algebraic spaces over `S`, then for every `y` in `Points Y` the set of
points of `Points X` lying over `y` at which `f` is quasi-finite is finite. -/
@[stacks 0ABN]
theorem FiniteType.finiteQuasiFiniteAtPointsOver {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [FiniteType f] (y : Points Y) :
    (setOf fun x : Points X ↦ Points.map f x = y ∧ QuasiFiniteAt f x).Finite := sorry

end AlgebraicGeometry.AlgebraicSpace
