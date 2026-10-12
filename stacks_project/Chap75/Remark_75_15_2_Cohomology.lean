/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.Lemma_75_15_1_Extension

/-!
# Cohomology control for supported retract extensions

A supported perfect extension of a map from a perfect object on a quasi-compact
open subspace can be chosen so that the retract inclusion induces cohomology-sheaf
isomorphisms in every degree strictly above a prescribed cutoff.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- A supported perfect extension of `α : P ⟶ E|_W` can be chosen so that the
retract inclusion `P ⟶ R|_W` induces cohomology-sheaf isomorphisms in every
degree strictly above a prescribed cutoff. The source's finite shift-biproduct
form `R|_W = P ⊕ ⨁ j, P^{⊕ n_j}⟦j⟧` and the agreement of highest cohomology
are the proof's intermediate presentation of this strengthening. -/
theorem exists_supported_retract_extension_isIso_above {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (W : OpenSubspace X) [IsQuasiCompact W.X] (T : Closeds (Points X))
    (hT : QuasiCompact (OpenSubspace.ofOpensι T.compl)) (E : DerivedQCoh X)
    (P : ModuleDerived W.X) (hP : ModuleDerived.IsPerfect P)
    (hP_support :
      ModuleDerived.IsSupportedOn P (Points.map W.ι ⁻¹' (T : Set (Points X))))
    (α : P ⟶ (ModuleDerived.pullback W.ι).obj E.obj) (a : ℤ) :
    ∃ (R : ModuleDerived X) (hR : ModuleDerived.IsPerfect R)
      (hR_support : ModuleDerived.IsSupportedOn R (T : Set (Points X)))
      (β : R ⟶ E.obj) (r : Retract P ((ModuleDerived.pullback W.ι).obj R)),
      r.i ≫ (ModuleDerived.pullback W.ι).map β = α ∧
        ∀ i : ℤ, a < i →
          IsIso ((DerivedCategory.homologyFunctor (Modules W.X) i).map r.i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
