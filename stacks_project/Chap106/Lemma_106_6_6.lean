/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap106.Lemma_106_6_6_Comparison

/-!
# Étale-local isomorphism of smooth cartesian lifts along a thickening

Two 2-cartesian smooth lifts of algebraic spaces along a thickening of
algebraic stacks become isomorphic after passage to an étale covering of the
thickened source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack Limits Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Lift

/-- Lemma 106.6.6. Let `iX : X ⟶ X'` be a thickening of algebraic stacks.
Consider a 2-commutative diagram of cartesian squares with algebraic spaces
`W`, `W'`, `W''` and smooth vertical maps `x`, `x'`, `x''`. Then there exist
an étale covering `{f' k : Wk k ⟶ W'}`, étale maps `f'' k : Wk k ⟶ W''`, and
2-isomorphisms
`γ k : toGroupoids.map (f'' k) ≫ x'' ≅ toGroupoids.map (f' k) ≫ x'`
such that (a) the inverse images of `W` agree, (b) the two maps restrict
equally on that inverse image, and (c) restriction of `γ k` agrees with the
2-morphism over `W` coming from the original diagram. -/
@[stacks 0CJW]
theorem exists_etaleCovering_iso {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (iX : X ⟶ X') [IsThickening iX]
    {W W' W'' : AlgebraicSpace S} (x : W.toGroupoids ⟶ X)
    (x' : W'.toGroupoids ⟶ X') (x'' : W''.toGroupoids ⟶ X')
    [Groupoids.Hom.Smooth x] [Groupoids.Hom.Smooth x'] [Groupoids.Hom.Smooth x'']
    (i : W ⟶ W') (i'' : W ⟶ W'')
    (α' : x ≫ iX ≅ AlgebraicSpace.toGroupoids.map i ≫ x')
    (α'' : x ≫ iX ≅ AlgebraicSpace.toGroupoids.map i'' ≫ x'')
    (h' : PseudoPullbackCone.IsBilimit
      (⟨W.toGroupoids, x, AlgebraicSpace.toGroupoids.map i, α'⟩ :
        PseudoPullbackCone iX x'))
    (h'' : PseudoPullbackCone.IsBilimit
      (⟨W.toGroupoids, x, AlgebraicSpace.toGroupoids.map i'', α''⟩ :
        PseudoPullbackCone iX x'')) :
    ∃ (ι : Type u) (Wk : ι → AlgebraicSpace S) (f' : ∀ k, Wk k ⟶ W')
      (f'' : ∀ k, Wk k ⟶ W'')
      (γ : ∀ k, AlgebraicSpace.toGroupoids.map (f'' k) ≫ x'' ≅
        AlgebraicSpace.toGroupoids.map (f' k) ≫ x'),
      IsEtaleLocalIso α' α'' f' f'' γ :=
  sorry

/-- The covering in `exists_etaleCovering_iso` may equivalently be unpacked as
an étale covering of `W'`, étale maps `f'' k`, inverse-image pullback squares,
and restriction of each `γ k` to the over-`W` 2-morphism. -/
theorem exists_etaleCovering_iso_spec {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (iX : X ⟶ X') [IsThickening iX]
    {W W' W'' : AlgebraicSpace S} (x : W.toGroupoids ⟶ X)
    (x' : W'.toGroupoids ⟶ X') (x'' : W''.toGroupoids ⟶ X')
    [Groupoids.Hom.Smooth x] [Groupoids.Hom.Smooth x'] [Groupoids.Hom.Smooth x'']
    (i : W ⟶ W') (i'' : W ⟶ W'')
    (α' : x ≫ iX ≅ AlgebraicSpace.toGroupoids.map i ≫ x')
    (α'' : x ≫ iX ≅ AlgebraicSpace.toGroupoids.map i'' ≫ x'')
    (h' : PseudoPullbackCone.IsBilimit
      (⟨W.toGroupoids, x, AlgebraicSpace.toGroupoids.map i, α'⟩ :
        PseudoPullbackCone iX x'))
    (h'' : PseudoPullbackCone.IsBilimit
      (⟨W.toGroupoids, x, AlgebraicSpace.toGroupoids.map i'', α''⟩ :
        PseudoPullbackCone iX x'')) :
    ∃ (ι : Type u) (Wk : ι → AlgebraicSpace S) (f' : ∀ k, Wk k ⟶ W')
      (f'' : ∀ k, Wk k ⟶ W'')
      (γ : ∀ k, AlgebraicSpace.toGroupoids.map (f'' k) ≫ x'' ≅
        AlgebraicSpace.toGroupoids.map (f' k) ≫ x'),
      AlgebraicSpace.EtaleCovering (fun k ↦ Over.mk (f' k)) ∧
        (∀ k, AlgebraicSpace.Etale (f'' k)) ∧
        (∀ k, IsPullback (pullback.fst i (f' k)) (pullback.snd i (f' k))
            i'' (f'' k)) ∧
        (∀ k (hPB : IsPullback (pullback.fst i (f' k)) (pullback.snd i (f' k))
            i'' (f'' k)),
          RestrictsToOverW α' α'' (γ k) hPB.w) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Lift
