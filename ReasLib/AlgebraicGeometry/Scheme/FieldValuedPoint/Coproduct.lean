/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Field-valued points of arbitrary scheme coproducts

The inverse reads the actual coproduct branch of the unique source point, then
uses the native open-immersion lift to recover the point on that summand.
-/

@[expose] public section
open CategoryTheory Limits AlgebraicGeometry
noncomputable section
universe u
namespace AlgebraicGeometry.Scheme.FieldValuedPoint

variable {X : Scheme.{u}} {K : Type u} [Field K]
variable {ι : Type u} (Y : ι → Scheme.{u}) (p : ∀ i, Y i ⟶ X)
variable (point : Spec (.of K) ⟶ X)

def fibreBranch (t : Over.mk point ⟶ Over.mk (Sigma.desc p)) : ι :=
  ((AlgebraicGeometry.sigmaMk Y).symm (t.left (default : Spec (.of K)))).1

theorem fibreBranch_range (t : Over.mk point ⟶ Over.mk (Sigma.desc p)) :
    Set.range t.left ⊆ Set.range (Sigma.ι Y (fibreBranch Y p point t)) := by
  rintro _ ⟨z, rfl⟩
  change Spec (.of K) at z
  have hz : z = (default : Spec (.of K)) := Subsingleton.elim _ _
  subst z
  let q := (AlgebraicGeometry.sigmaMk Y).symm (t.left (default : Spec (.of K)))
  exact ⟨q.2, by
    change Sigma.ι Y q.1 q.2 = t.left (default : Spec (.of K))
    rw [← AlgebraicGeometry.sigmaMk_mk]
    exact (AlgebraicGeometry.sigmaMk Y).apply_symm_apply _⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
def fibreBranchPoint (t : Over.mk point ⟶ Over.mk (Sigma.desc p)) :
    Over.mk point ⟶ Over.mk (p (fibreBranch Y p point t)) := by
  letI : IsOpenImmersion (Sigma.ι Y (fibreBranch Y p point t)) :=
    inferInstanceAs (IsOpenImmersion ((AlgebraicGeometry.sigmaOpenCover Y).f _))
  let q := IsOpenImmersion.lift (Sigma.ι Y (fibreBranch Y p point t)) t.left
    (fibreBranch_range Y p point t)
  exact Over.homMk q (w := by
    change q ≫ p (fibreBranch Y p point t) = point
    calc
      q ≫ p (fibreBranch Y p point t) =
          q ≫ (Sigma.ι Y (fibreBranch Y p point t) ≫ Sigma.desc p) := by rw [Sigma.ι_desc]
      _ = t.left ≫ Sigma.desc p := by rw [← Category.assoc, IsOpenImmersion.lift_fac]
      _ = point := Over.w t)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
def sigmaFibreEquiv :
    (Σ i, (Over.mk point ⟶ Over.mk (p i))) ≃ (Over.mk point ⟶ Over.mk (Sigma.desc p)) where
  toFun z := Over.homMk (z.2.left ≫ Sigma.ι Y z.1) (w := by
    change (z.2.left ≫ Sigma.ι Y z.1) ≫ Sigma.desc p = point
    rw [Category.assoc, Sigma.ι_desc]
    exact Over.w z.2)
  invFun t := ⟨fibreBranch Y p point t, fibreBranchPoint Y p point t⟩
  left_inv := sorry
  right_inv := sorry

/-- Étale coproduct structure maps use native locality at the source. -/
theorem etale_sigmaDesc [∀ i, Etale (p i)] : Etale (Sigma.desc p) :=
  IsZariskiLocalAtSource.sigmaDesc (P := @Etale) (fun i ↦ inferInstance)

end AlgebraicGeometry.Scheme.FieldValuedPoint
