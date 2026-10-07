module

public import Mathlib.CategoryTheory.Retract
public import Mathlib.Topology.Sets.Closeds
public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Lemma_66_20_1_Sheaf
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Remark_67_12_5_Opens
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation
public import stacks_project.Chap75.Lemma_75_5_2_EtaleLocal

/-!
# Extending maps from supported perfect complexes on open subspaces

On a quasi-compact quasi-separated algebraic space, a map from a perfect object of
`D(𝒪_W)` supported on the preimage of a closed subset whose complement immersion is
quasi-compact extends to a map from a globally perfect object supported on that closed
subset, so that the original object is a compatible retract of the restriction.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- A map `α : P ⟶ E|_W` from a perfect object of `D(𝒪_W)` supported on `T ∩ W`
extends to a map `β : R ⟶ E` from a perfect object of `D(𝒪_X)` supported on `T`,
so that `P` is a direct summand of `R|_W` in `D(𝒪_W)` compatible with `α` and
`β|_W`. -/
theorem exists_supported_retract_extension {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] (W : OpenSubspace X)
    [IsQuasiCompact W.X] (T : Closeds (Points X))
    (hT : QuasiCompact (OpenSubspace.ofOpensι T.compl)) (E : DerivedQCoh X)
    (P : ModuleDerived W.X) (hP : ModuleDerived.IsPerfect P)
    (hP_support :
      ModuleDerived.IsSupportedOn P (Points.map W.ι ⁻¹' (T : Set (Points X))))
    (α : P ⟶ (ModuleDerived.pullback W.ι).obj E.obj) :
    ∃ (R : ModuleDerived X) (hR : ModuleDerived.IsPerfect R)
      (hR_support : ModuleDerived.IsSupportedOn R (T : Set (Points X)))
      (β : R ⟶ E.obj) (r : Retract P ((ModuleDerived.pullback W.ι).obj R)),
      r.i ≫ (ModuleDerived.pullback W.ι).map β = α := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
