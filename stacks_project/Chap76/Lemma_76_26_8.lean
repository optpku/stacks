/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Coproduct.ClopenCover
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeDimension.OpenSubspace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeDimension.CohenMacaulay
import StacksCheckRecall

/-!
# Clopen relative-dimension decomposition of Cohen-Macaulay morphisms

A locally finitely presented Cohen-Macaulay morphism of algebraic spaces
decomposes its source as a coproduct of open-and-closed subspaces of constant
relative dimension, in the sense of Stacks Lemma 76.26.8.
-/

open CategoryTheory AlgebraicGeometry AlgebraicSpace TopologicalSpace

universe u

/- Lemma 76.26.8: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. If `f` is locally of finite presentation and
Cohen-Macaulay, then there exist open and closed subspaces `X_d ⊂ X`,
indexed by `d ≥ 0`, such that `X` is the coproduct of the `X_d` and the
restriction `(U d).ι ≫ f : (U d).X ⟶ Y` has relative dimension `d`. -/
@[stacks 0E11] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_clopen_relativeDimension_decomposition :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [LocallyOfFinitePresentation f] [CohenMacaulay f],
    ∃ U : ℕ → OpenSubspace X,
      (⋃ d, (U d).pointsSet) = Set.univ ∧
        Pairwise (fun d e ↦ Disjoint (U d).pointsSet (U e).pointsSet) ∧
        (∀ d, IsClopen (U d).pointsSet) ∧
        ∀ d, RelativeDimension ((U d).ι ≫ f) d)

/- A pairwise disjoint clopen cover of `|X|` by open subspaces exhibits `X` as
the coproduct of those subspaces. -/
#check (AlgebraicGeometry.AlgebraicSpace.isIso_coproductDesc_of_clopen_cover :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (U : ℕ → OpenSubspace X),
      (⋃ d, (U d).pointsSet) = Set.univ →
      Pairwise (fun d e ↦ Disjoint (U d).pointsSet (U e).pointsSet) →
      (∀ d, IsClopen (U d).pointsSet) →
      IsIso (coproductDesc fun d ↦ (U d).ι))

/- Membership in a relative-dimension-`d` open subspace implies relative
dimension `d` for the ambient morphism at that point. -/
#check (AlgebraicGeometry.AlgebraicSpace.relativeDimensionAt_of_mem_pointsSet :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
      {U : OpenSubspace X} {d : ℕ}, RelativeDimension (U.ι ≫ f) d →
      ∀ {x : Points X}, x ∈ U.pointsSet → RelativeDimensionAt f d x)
