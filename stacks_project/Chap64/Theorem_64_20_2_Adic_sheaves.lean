/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap64.Definition_64_19_3_LFunction
public import stacks_project.Chap64.Theorem_64_20_2_Adic_sheaves_Euler

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.SchemeOverField

namespace AlgebraicGeometry.Scheme.Etale
namespace ZEllSheaf

variable {k : Type u} [Field k] [Fintype k]
variable {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
variable {ℓ : ℕ} [Fact ℓ.Prime]
variable {X : SchemeOverField k} [Scheme.Hom.FiniteType X.hom] [IsNoetherian X.left]
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
  HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]
variable (P : Compactification.Of (Spec (CommRingCat.of k)) X)
variable [Etale (Compactification.Of.ι P)]
variable [∀ G : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension G]
variable [HasWeakSheafify (Scheme.smallEtaleTopology (Over.left P.obj.right)) AddCommGrpCat.{u}]
variable [HasSheafify (Scheme.smallEtaleTopology (Over.left P.obj.right)) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Scheme.smallEtaleTopology (Over.left P.obj.right)) AddCommGrpCat.{u})]
variable [∀ Z : Scheme.{u}, HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable (F : ZEllSheaf X.left ℓ)

/-- Theorem 64.20.2 (Adic sheaves): the closed-point Euler product L-function of
a constructible `ℚ_[ℓ]`-sheaf equals the signed product of geometric Frobenius
Euler factors on compactly supported cohomology. `P` presents compact support
and `N` is a cohomological vanishing bound. -/
@[stacks 03V0]
theorem lFunction_eq_prod_det_geometricFrobenius (hF : F.IsConstructible) (N : ℕ)
    (hN : ∀ i, N < i →
      Module.finrank ℚ_[ℓ] (geometricCohomologyCompactSupportQEll P F i) = 0) :
    F.lFunction hF = cohomologicalLFunction P F N := sorry

end ZEllSheaf
end AlgebraicGeometry.Scheme.Etale
