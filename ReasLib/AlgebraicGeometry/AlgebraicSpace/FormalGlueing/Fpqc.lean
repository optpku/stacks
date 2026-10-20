/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormalGlueing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fpqc

/-! # Fpqc refinements for formal glueing of algebraic spaces -/

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

/-- A formal-glueing morphism and the inclusion of the complement of its
finite-presentation closed immersion admit a refining fpqc covering. -/
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
