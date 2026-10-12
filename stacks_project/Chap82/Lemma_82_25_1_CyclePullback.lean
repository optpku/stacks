/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_33_2_RelativeDimension
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap76.Lemma_76_32_2
public import stacks_project.Chap82.Definition_82_3_1_CycleGroup
import stacks_project.Chap82.Lemma_82_10_4_Pullback

/-!
# Cycle-level flat pullback, import-isolated

`Hom.cycleFlatPullback` is definitionally `Hom.flatPullbackHom`, but
`Lemma_82_10_4_Pullback` re-exports `Hom.closedSubspaceDeltaDimension` from
Definition 82.5.2 and cannot be loaded beside Chow groups. This module exposes
the cycle-level operator without re-exporting the conflicting dimension names.
-/

public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- Flat pullback of `k`-cycles along a morphism of relative dimension `r`, as
an additive map `Z_k(Y) → Z_{k+r}(X)`. -/
noncomputable def cycleFlatPullback {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ) :
    cycleGroup pY δ k →+ cycleGroup pX δ (k + (r : ℤ)) :=
  flatPullbackHom pY pX δ f r hf k

/-- Cycle-level flat pullback sends the zero cycle to zero. -/
theorem cycleFlatPullback_zero {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) (k : ℤ) :
    cycleFlatPullback pY pX δ f r hf k 0 = 0 :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
