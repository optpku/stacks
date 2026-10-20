module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormalGlueing.Fpqc
import StacksCheckRecall

/-!
# Lemma 81.10.11

In Situation 81.10.6, the two-arrow family `{U ⟶ X, Y ⟶ X}` with
`U = closedImmersionComplement i` admits a refining fpqc covering of `X`.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.SemiRepresentableFamily.Over

universe u

/- Lemma 81.10.11: In Situation 81.10.6 there exists an fpqc covering
`{X_i ⟶ X}_{i ∈ I}` refining the family `{U ⟶ X, Y ⟶ X}`, where
`U` is `closedImmersionComplement i`. -/
@[stacks 0AF1] #check
  (AlgebraicGeometry.AlgebraicSpace.IsFormalGlueing.exists_fpqcCovering_refinement :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X),
    [QuasiCompact f] → [QuasiSeparated f] → [IsClosedImmersion i] →
    [FinitePresentation i] → [IsFormalGlueing f i] →
    ∃ 𝒰 : SemiRepresentableFamily.Over.{u + 1} X,
      FpqcCovering 𝒰.obj ∧ Refines 𝒰 (complementSourceFamily f i))

