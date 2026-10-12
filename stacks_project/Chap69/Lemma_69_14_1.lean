/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Topology.Sets.Closeds
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap67.Lemma_67_31_6_ModuleSupport
public import stacks_project.Chap69.Definition_69_12_1_Instances

/-!
# Lemma 69.14.1

A coherent module on a Noetherian algebraic space whose support is a union of two
closed subsets admits a short exact decomposition into coherent modules supported
on the respective subsets.
-/

@[expose]
public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 69.14.1: let `S` be a scheme, let `X` be a Noetherian algebraic space over `S`,
and let `F` be a coherent `𝒪_X`-module. If `moduleSupport F = Z ∪ Z'` for closed subsets
`Z`, `Z'` of `Points X`, then there is a short exact sequence `0 ⟶ G' ⟶ F ⟶ G ⟶ 0`
of coherent sheaves with `moduleSupport G' ⊆ Z'` and `moduleSupport G ⊆ Z`. -/
@[stacks 07UP]
theorem exists_shortExact_of_support_eq_union
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
    (F : X.Modules) [F.IsCoherent]
    (Z Z' : TopologicalSpace.Closeds (Points X))
    (hSupp : moduleSupport F = (Z : Set (Points X)) ∪ (Z' : Set (Points X))) :
    ∃ (G' G : X.Modules) (hG' : SheafOfModules.IsCoherent G')
      (hG : SheafOfModules.IsCoherent G)
      (ι : G' ⟶ F) (π : F ⟶ G) (w : ι ≫ π = 0)
      (hSuppG : moduleSupport G ⊆ (Z : Set (Points X))),
      (ShortComplex.mk ι π w).ShortExact ∧
        moduleSupport G' ⊆ (Z' : Set (Points X)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
