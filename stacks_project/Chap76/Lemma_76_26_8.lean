module

public import Mathlib.Topology.Defs.Basic
public import stacks_project.Chap65.Lemma_65_8_4_Coproduct
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap67.Definition_67_33_2_RelativeDimension
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap76.Lemma_76_26_3_CohenMacaulay

/-!
# Clopen relative-dimension decomposition of Cohen-Macaulay morphisms

A locally finitely presented Cohen-Macaulay morphism of algebraic spaces
decomposes its source as a coproduct of open-and-closed subspaces of constant
relative dimension, in the sense of Stacks Lemma 76.26.8.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.26.8: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. If `f` is locally of finite presentation and
Cohen-Macaulay, then there exist open and closed subspaces `X_d ⊂ X`,
indexed by `d ≥ 0`, such that `X` is the coproduct of the `X_d` and the
restriction `(U d).ι ≫ f : (U d).X ⟶ Y` has relative dimension `d`. -/
@[stacks 0E11]
theorem exists_clopen_relativeDimension_decomposition
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [CohenMacaulay f] :
    ∃ U : ℕ → OpenSubspace X,
      (⋃ d, (U d).pointsSet) = Set.univ ∧
        Pairwise (fun d e ↦ Disjoint (U d).pointsSet (U e).pointsSet) ∧
        (∀ d, IsClopen (U d).pointsSet) ∧
        ∀ d, RelativeDimension ((U d).ι ≫ f) d :=
  sorry

/-- A pairwise disjoint clopen cover of `|X|` by open subspaces exhibits `X` as
the coproduct of those subspaces. -/
theorem isIso_coproductDesc_of_clopen_cover
    {S : Scheme.{u}} {X : AlgebraicSpace S} (U : ℕ → OpenSubspace X)
    (h_cover : (⋃ d, (U d).pointsSet) = Set.univ)
    (h_disjoint : Pairwise (fun d e ↦ Disjoint (U d).pointsSet (U e).pointsSet))
    (h_clopen : ∀ d, IsClopen (U d).pointsSet) :
    IsIso (coproductDesc fun d ↦ (U d).ι) :=
  sorry

/-- Membership in a relative-dimension-`d` open subspace implies relative
dimension `d` for the ambient morphism at that point. -/
theorem relativeDimensionAt_of_mem_pointsSet
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {U : OpenSubspace X} {d : ℕ} (h_dim : RelativeDimension (U.ι ≫ f) d)
    {x : Points X} (hx : x ∈ U.pointsSet) :
    RelativeDimensionAt f d x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
