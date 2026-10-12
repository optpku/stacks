/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Variety
public import stacks_project.Chap64.Theorem_64_20_2_Adic_sheaves_Euler
public import stacks_project.Chap64.Theorem_64_27_4_Deligne_Weil_II_Cohomology
public import stacks_project.Chap64.Theorem_64_27_4_Deligne_Weil_II_Weight
import Mathlib.Tactic.CrossRefAttribute

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

/-- Theorem 64.27.4 (Deligne, Weil II) (1): if `F` is a lisse `ℚ_[ℓ]`-sheaf on a
variety `X` over a finite field `k` with `#k = q` and `ℓ ≠ p`, identified with
the sheaf `F_ρ` attached to a continuous representation satisfying Deligne's
conclusions, then every eigenvalue `α` of `π_X^*` on the finite-dimensional
space `H_c^i(X_k̄, F_ρ)` is algebraic with `|α| = q^{w/2}` for some `w ∈ ℤ`,
`w ≤ i`. -/
@[stacks 03VH]
theorem geometricFrobenius_isMixedOfWeightsLE (hℓp : ℓ ≠ p) (hF_lisse : F.IsLisse)
    (hF_deligne : F.SatisfiesDeligneConclusions) (i : ℕ) :
    (geometricFrobenius_cohomologyCompactSupportQEll P F i).IsMixedOfWeightsLE
      (Fintype.card k) i := sorry

/-- Theorem 64.27.4 (Deligne, Weil II) (2): in the situation of
`geometricFrobenius_isMixedOfWeightsLE`, if `X` is moreover smooth and projective over
`k`, then every eigenvalue of `π_X^*` on the finite-dimensional space
`H_c^i(X_k̄, F_ρ)` is pure of weight `i`. -/
@[stacks 03VH]
theorem geometricFrobenius_isPureOfWeight (hℓp : ℓ ≠ p) (hF_lisse : F.IsLisse)
    (hF_deligne : F.SatisfiesDeligneConclusions) [Smooth X.hom] [Projective X.hom]
    (i : ℕ) :
    (geometricFrobenius_cohomologyCompactSupportQEll P F i).IsPureOfWeight
      (Fintype.card k) i := sorry
