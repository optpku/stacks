module

public import stacks_project.Chap73.Definition_73_9_1_FpqcCovering
public import stacks_project.Chap81.Situation_81_10_6_FormalGlueing

/-!
# Lemma 81.10.11

In Situation 81.10.6, the two-arrow family `{U ⟶ X, Y ⟶ X}` with
`U = closedImmersionComplement i` admits a refining fpqc covering of `X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.SemiRepresentableFamily.Over

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The two-arrow family `{closedImmersionComplementι i, f}` with common target `X`,
indexed by `Bool` with `false` the complement inclusion of `i` and `true` the source
morphism `f`. -/
def complementSourceFamily {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] :
    SemiRepresentableFamily.Over.{0} X :=
  ofArrows (fun b : Bool ↦ if b then Y else closedImmersionComplement i)
    (fun b ↦ match b with
      | true => f
      | false => closedImmersionComplementι i)

/-- The members of `complementSourceFamily f i` are the complement inclusion
`closedImmersionComplementι i` and the source morphism `f`. -/
theorem complementSourceFamily_obj {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] :
    (complementSourceFamily f i).obj false = Over.mk (closedImmersionComplementι i) ∧
      (complementSourceFamily f i).obj true = Over.mk f :=
  sorry

namespace IsFormalGlueing

/-- Lemma 81.10.11: In Situation 81.10.6 there exists an fpqc covering
`{X_i ⟶ X}_{i ∈ I}` refining the family `{U ⟶ X, Y ⟶ X}`, where
`U` is `closedImmersionComplement i`. -/
@[stacks 0AF1]
theorem exists_fpqcCovering_refinement {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] :
    ∃ 𝒰 : SemiRepresentableFamily.Over.{u + 1} X,
      FpqcCovering 𝒰.obj ∧ Refines 𝒰 (complementSourceFamily f i) :=
  sorry

end IsFormalGlueing

end AlgebraicGeometry.AlgebraicSpace

