/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Variety
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.GeometricCompactSupport
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.Deligne
public import ReasLib.LinearAlgebra.Charpoly.Weights

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
variable (F : ZEllSheaf X.left ℓ)

/-- Geometric Frobenius on compactly supported rational adic cohomology of a
finite-field variety with a lisse sheaf satisfying Deligne's conclusions has
algebraic eigenvalues of integer weights at most the cohomological degree. -/
theorem geometricFrobenius_isMixedOfWeightsLE (hℓp : ℓ ≠ p) (hF_lisse : F.IsLisse)
    (hF_deligne : F.SatisfiesDeligneConclusions (p := p)) (i : ℕ) :
    (geometricFrobenius_cohomologyCompactSupportQEll P F i).IsMixedOfWeightsLE
      (Fintype.card k) i := sorry

/-- Geometric Frobenius on compactly supported rational adic cohomology of a
smooth projective finite-field variety with a lisse sheaf satisfying Deligne's
conclusions has algebraic eigenvalues pure of the cohomological degree. -/
theorem geometricFrobenius_isPureOfWeight (hℓp : ℓ ≠ p) (hF_lisse : F.IsLisse)
    (hF_deligne : F.SatisfiesDeligneConclusions (p := p)) [Smooth X.hom] [Projective X.hom]
    (i : ℕ) :
    (geometricFrobenius_cohomologyCompactSupportQEll P F i).IsPureOfWeight
      (Fintype.card k) i := sorry

end AlgebraicGeometry.Scheme.Etale.ZEllSheaf
