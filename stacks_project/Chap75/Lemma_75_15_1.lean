/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.Lemma_75_15_1_Extension
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Lemma 75.15.1: on a quasi-compact quasi-separated algebraic space `X` over a
scheme `S`, a map `α : P ⟶ E|_W` from a perfect object of `D(𝒪_W)` supported on
`T ∩ W` extends to a map `β : R ⟶ E` from a perfect object of `D(𝒪_X)` supported
on `T`, so that `P` is a direct summand of `R|_W` in `D(𝒪_W)` compatible with `α`
and `β|_W`. -/
@[stacks 09IV]
#check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.exists_supported_retract_extension :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      (W : OpenSubspace X) [IsQuasiCompact W.X]
      (T : Closeds (Points X)) (hT : QuasiCompact (OpenSubspace.ofOpensι T.compl))
      (E : DerivedQCoh X) (P : ModuleDerived W.X)
      (hP : ModuleDerived.IsPerfect P)
      (hP_support :
        ModuleDerived.IsSupportedOn P (Points.map W.ι ⁻¹' (T : Set (Points X))))
      (α : P ⟶ (ModuleDerived.pullback W.ι).obj E.obj),
      ∃ (R : ModuleDerived X) (hR : ModuleDerived.IsPerfect R)
        (hR_support : ModuleDerived.IsSupportedOn R (T : Set (Points X)))
        (β : R ⟶ E.obj) (r : Retract P ((ModuleDerived.pullback W.ι).obj R)),
        r.i ≫ (ModuleDerived.pullback W.ι).map β = α)
