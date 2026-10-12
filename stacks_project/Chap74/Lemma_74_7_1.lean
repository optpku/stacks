/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap73.Definition_73_9_1_FpqcCovering
public import stacks_project.Chap74.Lemma_74_7_1_InverseImage

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

namespace FpqcCovering

/-- Lemma 74.7.1: let `S` be a scheme and `{f_i : T_i ⟶ T}` an fpqc covering of
algebraic spaces over `S`. If `W i ⊂ T_i` are open subspaces such that
`(W i).inverseImage (pullback.fst (family i).hom (family j).hom)` and
`(W j).inverseImage (pullback.snd (family i).hom (family j).hom)` have equal
point-sets as open subspaces of `T_i ×_T T_j` for all `i, j`, then there exists
a unique open `V` of `|T|` with
`(W i).pointsSet = Points.map (family i).hom ⁻¹' V.carrier` for every `i`. -/
@[stacks 04P1]
theorem existsUnique_open {S : Scheme.{u}} {T : AlgebraicSpace S} {ι : Type v}
    {family : ι → Over T} (hfamily : FpqcCovering family)
    (W : (i : ι) → OpenSubspace (family i).left)
    (hcompat : ∀ i j : ι,
      ((W i).inverseImage (pullback.fst (family i).hom (family j).hom)).pointsSet =
        ((W j).inverseImage (pullback.snd (family i).hom (family j).hom)).pointsSet) :
    ∃! V : Opens (Points T),
      ∀ i : ι,
        (W i).pointsSet =
          Points.map (family i).hom ⁻¹' V.carrier :=
  sorry

/-- Compatible open subspaces on an fpqc covering family arise as inverse images
of an open subspace of the target, unique up to unique lift over the target. -/
theorem existsUnique_openSubspace {S : Scheme.{u}} {T : AlgebraicSpace S} {ι : Type v}
    {family : ι → Over T} (hfamily : FpqcCovering family)
    (W : (i : ι) → OpenSubspace (family i).left)
    (hcompat : ∀ i j : ι,
      ((W i).inverseImage (pullback.fst (family i).hom (family j).hom)).pointsSet =
        ((W j).inverseImage (pullback.snd (family i).hom (family j).hom)).pointsSet) :
    ∃ U : OpenSubspace T,
      (∀ i : ι,
          (W i).pointsSet = (U.inverseImage (family i).hom).pointsSet) ∧
        ∀ U' : OpenSubspace T,
          (∀ i : ι,
              (W i).pointsSet = (U'.inverseImage (family i).hom).pointsSet) →
            ∃! φ : U'.X ⟶ U.X, φ ≫ U.ι = U'.ι :=
  sorry

end FpqcCovering

end AlgebraicGeometry.AlgebraicSpace
