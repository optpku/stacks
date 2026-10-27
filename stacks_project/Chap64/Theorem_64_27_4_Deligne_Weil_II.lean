/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Weights
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open ZEllSheaf
open scoped AlgebraicGeometry

noncomputable section

universe u

variable {k : Type u} [Field k] [Fintype k]
variable {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
variable {ℓ : ℕ} [Fact ℓ.Prime]
variable {X : SchemeOverField k} [Variety X] [IsNoetherian X.left] [ConnectedSpace X.left]
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Z : Scheme.{u}) (V : Z.Etale),
    HasWeakSheafify (Z.smallEtaleTopology.over V) AddCommGrpCat.{u}]
variable (P : Compactification.Of (Spec (CommRingCat.of k)) X)
variable [Etale (Compactification.Of.ι P)]
variable [∀ G : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
    (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension G]
variable [HasWeakSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable (F : ZEllSheaf X.left ℓ)

/- Theorem 64.27.4 (Deligne, Weil II)
Geometric Frobenius eigenvalues have integer weights at most the cohomological degree. -/
@[stacks 03VH] #check
  (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.geometricFrobenius_isMixedOfWeightsLE P F :
    ℓ ≠ p → F.IsLisse → F.SatisfiesDeligneConclusions (p := p) → ∀ (i : ℕ),
      (geometricFrobenius_cohomologyCompactSupportQEll P F i).IsMixedOfWeightsLE
        (Fintype.card k) i)

/- Theorem 64.27.4 (Deligne, Weil II)
For smooth projective varieties the weight equals the cohomological degree. -/
@[stacks 03VH] #check
  (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.geometricFrobenius_isPureOfWeight P F :
    ℓ ≠ p → F.IsLisse → F.SatisfiesDeligneConclusions (p := p) →
      ∀ [Smooth X.hom] [Projective X.hom] (i : ℕ),
      (geometricFrobenius_cohomologyCompactSupportQEll P F i).IsPureOfWeight
        (Fintype.card k) i)
