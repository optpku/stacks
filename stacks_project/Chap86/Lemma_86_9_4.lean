/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap86.Lemma_86_9_4_Covering
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeDualizingComplex
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open CategoryTheory CategoryTheory.Limits

universe u v

/- Lemma 86.9.4: let `S` be a scheme. Let `f : X ⟶ Y` be a proper, flat morphism of
algebraic spaces which is of finite presentation. Let `(ω, τ)` be a pair consisting of
a `Y`-perfect object of `D(𝒪_X)` and a map `τ : Rf_* ω ⟶ 𝒪_Y`. Assume there are
cartesian diagrams with `Y_i` affine such that `{g_i : Y_i ⟶ Y}` is an étale covering
and isomorphisms of pairs `(ω|_{X_i}, τ|_{Y_i}) ⟶ (a_i(𝒪_{Y_i}), Tr_{f_i})` as in
Definition 86.9.1. Then `(ω, τ)` is a relative dualizing complex for `X` over `Y`. -/
@[stacks 0E60] #check (RelativeDualizingComplex.ofEtaleCovering :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [Proper f] [Flat f] [FinitePresentation f]
    (ω : ModuleDerived X)
    (τ : (moduleDerivedPushforward f).obj ω ⟶ derivedStructureSheaf Y),
    IsPerfectRelativeTo f ω →
    ∀ {ι : Type v} {Yi : ι → AlgebraicSpace S} {Xi : ι → AlgebraicSpace S}
      (g' : ∀ i, Xi i ⟶ X) (fi : ∀ i, Xi i ⟶ Yi i) (g : ∀ i, Yi i ⟶ Y)
      (sq : ∀ i, IsPullback (g' i) (fi i) f (g i)),
      ((∀ i, Etale (g i)) ∧ (⋃ i, Set.range (Points.map (g i))) = Set.univ) →
      (∀ i, IsAffine (Yi i)) →
      (∀ (i : ι) [IsAffine (Yi i)] [QuasiCompact (fi i)] [QuasiSeparated (fi i)],
        affineBaseChangeOn f (g' i) (fi i) (g i) (sq i) ω τ) →
      RelativeDualizingComplex f)
