/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Weights
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.Deligne.Constant

/-!
# Cohomological weights for the constant rank-one coefficient

The constant-sheaf producer supplies Deligne's conclusions. The existing
conditional weight theorems retain the prime-to-characteristic and
compactification assumptions, and the pure case retains smoothness and
projectivity.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open ZEllSheaf
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.ZEllSheaf

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

/-- The constant rank-one coefficient supplies the Deligne input to the
existing compactly supported mixed-weight theorem. -/
theorem constant_geometricFrobenius_isMixedOfWeightsLE (hℓp : ℓ ≠ p) (i : ℕ) :
    (geometricFrobenius_cohomologyCompactSupportQEll P (constant X.left ℓ) i).IsMixedOfWeightsLE (Fintype.card k) i :=
  geometricFrobenius_isMixedOfWeightsLE P (constant X.left ℓ) hℓp
    constant_isLisse (constant_satisfiesDeligneConclusions p) i

/-- On a smooth projective variety, the constant rank-one coefficient supplies
the Deligne input to the existing pure-weight theorem. -/
theorem constant_geometricFrobenius_isPureOfWeight (hℓp : ℓ ≠ p)
    [Smooth X.hom] [Projective X.hom] (i : ℕ) :
    (geometricFrobenius_cohomologyCompactSupportQEll P (constant X.left ℓ) i).IsPureOfWeight (Fintype.card k) i :=
  geometricFrobenius_isPureOfWeight P (constant X.left ℓ) hℓp
    constant_isLisse (constant_satisfiesDeligneConclusions p) i

end AlgebraicGeometry.Scheme.Etale.ZEllSheaf
