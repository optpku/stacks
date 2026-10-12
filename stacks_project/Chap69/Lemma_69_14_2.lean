/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Topology.Sets.Closeds
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap67.Definition_67_14_4_IdealSubobject
public import stacks_project.Chap67.Definition_67_47_7_Irreducible
public import stacks_project.Chap67.Lemma_67_15_3_SchemeTheoreticSupport
public import stacks_project.Chap67.Lemma_67_31_6_ModuleSupport
public import stacks_project.Chap67.Lemma_67_48_6_Reduced
public import stacks_project.Chap69.Definition_69_12_1_Instances

/-!
# Lemma 69.14.2

On a Noetherian algebraic space, a coherent module whose scheme-theoretic support
is reduced with irreducible underlying space admits a dévissage step: a monomorphism
from the pushforward of a finite coproduct of a nonzero coherent ideal sheaf, with
cokernel supported on a proper closed subset of the support.
-/

@[expose]
public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 69.14.2: let `S` be a scheme, let `X` be a Noetherian algebraic space over
`S`, and let `F` be a coherent `𝒪_X`-module. If `i : Z ⟶ X` is a scheme-theoretic
support of `F` with `Z` reduced and `|Z|` irreducible, then there exist an integer
`r > 0`, a nonzero ideal sheaf `I ⊂ 𝒪_Z`, and a monomorphism
`(pushforward i).obj (∐ fun _ : Fin r ↦ I.toModule) ⟶ F` of coherent sheaves whose
cokernel is supported on a proper closed subspace of `Z`. -/
@[stacks 07UQ]
theorem exists_coherentIdeal_coproduct_pushforward_mono
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
    (F : X.Modules) [F.IsCoherent]
    {Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsSchemeTheoreticSupport F i] [IsReduced Z] [IsIrreducible Z] :
    ∃ (r : ℕ) (I : IdealSubobject Z)
      (φ : (pushforward i).obj (∐ fun _ : Fin r ↦ I.toModule) ⟶ F)
      (W : TopologicalSpace.Closeds (Points X)),
      0 < r ∧ I ≠ ⊥ ∧ I.toModule.IsCoherent ∧
        ((pushforward i).obj (∐ fun _ : Fin r ↦ I.toModule)).IsCoherent ∧
        Mono φ ∧ moduleSupport (cokernel φ) ⊆ (W : Set (Points X)) ∧
          (W : Set (Points X)) ⊂ Set.range (Points.map i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
