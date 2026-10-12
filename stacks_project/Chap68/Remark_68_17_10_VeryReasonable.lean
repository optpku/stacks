/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap68.Lemma_68_17_4_Relative

/-!
# Very reasonable algebraic spaces and morphisms

Definition 68.6.1 uses condition (2) of Lemma 68.4.7: a FAMILY of étale scheme charts
covers the space and each chart has quasi-compact self-relation projections.
No single globally quasi-compact atlas is required. Definition 68.17.1 applies this
object property after every base change by a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Definition 68.6.1, via Lemma 68.4.7 (2): a space is very reasonable when an étale
family of schemes jointly covers its points and each chart's self-fibre-product has
quasi-compact projections. The fibre products are exhibited by actual schemes and
pullback squares, not inferred from a vacuous universal condition on nonexistent limits.
The indexing universe contains all scheme charts over the fixed base, so no extra
small-family restriction is imposed. -/
class IsVeryReasonable {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop where
  /-- A covering family of étale charts with quasi-compact self-relation projections. -/
  exists_cover :
    ∃ (I : Type (u + 1)) (U : I → Over S) (p : ∀ i, ofOver (U i) ⟶ X),
      (∀ i, Etale (p i)) ∧ (⋃ i, Set.range (Points.map (p i))) = Set.univ ∧
        ∀ i, ∃ (R : Over S) (s t : R ⟶ U i),
          IsPullback (ofOverMap s) (ofOverMap t) (p i) (p i) ∧
            AlgebraicGeometry.QuasiCompact s.left ∧ AlgebraicGeometry.QuasiCompact t.left

namespace IsVeryReasonable

/-- The covering family and its actual self-relation pullback witnesses. -/
theorem spec {S : Scheme.{u}} (X : AlgebraicSpace S) [IsVeryReasonable X] :
    ∃ (I : Type (u + 1)) (U : I → Over S) (p : ∀ i, ofOver (U i) ⟶ X),
      (∀ i, Etale (p i)) ∧ (⋃ i, Set.range (Points.map (p i))) = Set.univ ∧
        ∀ i, ∃ (R : Over S) (s t : R ⟶ U i),
          IsPullback (ofOverMap s) (ofOverMap t) (p i) (p i) ∧
            AlgebraicGeometry.QuasiCompact s.left ∧ AlgebraicGeometry.QuasiCompact t.left :=
  IsVeryReasonable.exists_cover

/-- Every scheme is very reasonable: take its affine open covering; each chart is a
monomorphism, so its self-relation projections are isomorphisms and quasi-compact. -/
instance ofOver {S : Scheme.{u}} (T : Over S) : IsVeryReasonable (AlgebraicSpace.ofOver T) :=
  sorry

end IsVeryReasonable

/-- Definition 68.17.1 (4): a morphism is very reasonable if every scheme-base-change
of its source is a very reasonable algebraic space. -/
class VeryReasonable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop where
  /-- The apex of each scheme-base-change pullback square is very reasonable. -/
  ofOver_isPullback {T : Over S} {W : AlgebraicSpace S} {g : ofOver T ⟶ Y}
    {pT : W ⟶ ofOver T} {pX : W ⟶ X} :
    IsPullback pT pX g f → IsVeryReasonable W

namespace VeryReasonable

/-- Read the very-reasonable property from an actual scheme-base-change square. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} [VeryReasonable f]
    {T : Over S} {W : AlgebraicSpace S} {g : ofOver T ⟶ Y}
    {pT : W ⟶ ofOver T} {pX : W ⟶ X} (h : IsPullback pT pX g f) :
    IsVeryReasonable W :=
  VeryReasonable.ofOver_isPullback h

/-- The identity is very reasonable: its scheme-base-changes are isomorphic to schemes. -/
instance id {S : Scheme.{u}} (X : AlgebraicSpace S) : VeryReasonable (𝟙 X) := sorry

end VeryReasonable

end AlgebraicGeometry.AlgebraicSpace
