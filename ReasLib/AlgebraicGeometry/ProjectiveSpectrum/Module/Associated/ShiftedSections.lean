/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Graded.Shift.NatInt
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.Associated.Functorial
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
import Mathlib.Tactic.CrossRefAttribute

/-!
# Sections of shifted associated sheaves

Multiplication by a homogeneous scalar gives a morphism between the sheaves associated to
successive shifts of a graded module. Applying global sections supplies the canonical graded
action on the family of shifted section groups.
-/

@[expose] public section

open CategoryTheory
open TopologicalSpace
open scoped AlgebraicGeometry DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.Proj.AssociatedModule.ShiftedSections

variable {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
variable (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
variable (ℳ : ℤ → Submodule ℤ M) [SetLike.GradedSMul 𝒜 ℳ]
variable [DirectSum.Decomposition ℳ]

/-- The degree-n piece of shifted associated-sheaf sections. -/
@[stacks 0B5R "sections of a shifted associated sheaf"]
abbrev degree (n : ℤ) : Type u :=
  Γ(Proj.AssociatedModule.sheaf 𝒜 (GradedModule.shiftGrading ℳ n), ⊤)

/-- Multiplication by a degree-m scalar preserves the internal degree after shifting the
external index from n to (m : ℤ) + n. -/
theorem mulMapsTo {m : ℕ} (p : 𝒜 m) (n i : ℤ) :
    Set.MapsTo (LinearMap.lsmul A M (p : A))
      (GradedModule.shiftGrading ℳ n i)
      (GradedModule.shiftGrading ℳ ((m : ℤ) + n) i) := sorry

/-- The associated-sheaf morphism induced by multiplication by a homogeneous scalar. -/
@[stacks 0B5R "homogeneous action map between shifted associated sheaves"]
noncomputable def actionMap {m : ℕ} (p : 𝒜 m) (n : ℤ) :
    Proj.AssociatedModule.sheaf 𝒜 (GradedModule.shiftGrading ℳ n) ⟶
      Proj.AssociatedModule.sheaf 𝒜
        (GradedModule.shiftGrading ℳ ((m : ℤ) + n)) :=
  Proj.AssociatedModule.map
    (𝒜 := 𝒜) (ℳ := GradedModule.shiftGrading ℳ n)
    (ℵ := GradedModule.shiftGrading ℳ ((m : ℤ) + n))
    (LinearMap.lsmul A M (p : A))
    (mulMapsTo 𝒜 ℳ p n)

/-- The explicit homogeneous action on shifted associated-sheaf sections. -/
@[stacks 0B5R "explicit homogeneous action on shifted associated-sheaf sections"]
noncomputable def smul {m : ℕ} {n : ℤ}
    (p : 𝒜 m) (x : degree 𝒜 ℳ n) : degree 𝒜 ℳ ((m : ℤ) + n) :=
  (Scheme.Modules.globalSectionsMap (actionMap 𝒜 ℳ p n)).hom x

/-- Shifted associated-sheaf sections carry the explicit homogeneous scalar operation. -/
noncomputable instance instGSMul :
    GradedMonoid.GSMul (fun m : ℕ ↦ 𝒜 m) (degree 𝒜 ℳ) where
  smul := fun p x ↦ smul 𝒜 ℳ p x

/-- The degree-zero unit acts trivially on shifted associated-sheaf sections. -/
theorem one_smul (x : GradedMonoid (degree 𝒜 ℳ)) :
    (1 : GradedMonoid (fun m : ℕ ↦ 𝒜 m)) • x = x := sorry

/-- Successive homogeneous actions on shifted associated-sheaf sections compose as
multiplication. -/
theorem mul_smul (a b : GradedMonoid (fun m : ℕ ↦ 𝒜 m))
    (x : GradedMonoid (degree 𝒜 ℳ)) :
    (a * b) • x = a • b • x := sorry

/-- A homogeneous scalar distributes over addition of shifted associated-sheaf sections. -/
theorem smul_add {m : ℕ} {n : ℤ} (p : 𝒜 m)
    (x y : degree 𝒜 ℳ n) :
    smul 𝒜 ℳ p (x + y) = smul 𝒜 ℳ p x + smul 𝒜 ℳ p y := sorry

/-- A homogeneous scalar sends the zero shifted associated-sheaf section to zero. -/
theorem smul_zero {m : ℕ} {n : ℤ} (p : 𝒜 m) :
    smul 𝒜 ℳ p (0 : degree 𝒜 ℳ n) = 0 := sorry

/-- Addition of homogeneous scalars distributes through the shifted-section action. -/
theorem add_smul {m : ℕ} {n : ℤ} (p q : 𝒜 m)
    (x : degree 𝒜 ℳ n) :
    smul 𝒜 ℳ (p + q) x = smul 𝒜 ℳ p x + smul 𝒜 ℳ q x := sorry

/-- The zero homogeneous scalar acts by zero on shifted associated-sheaf sections. -/
theorem zero_smul {m : ℕ} {n : ℤ} (x : degree 𝒜 ℳ n) :
    smul 𝒜 ℳ (0 : 𝒜 m) x = 0 := sorry

/-- Shifted associated-sheaf sections form a graded multiplicative action. -/
noncomputable instance instGMulAction :
    GradedMonoid.GMulAction (fun m : ℕ ↦ 𝒜 m) (degree 𝒜 ℳ) where
  one_smul := one_smul 𝒜 ℳ
  mul_smul := mul_smul 𝒜 ℳ

/-- The homogeneous shifted-section action is additive in the section variable. -/
noncomputable instance instGdistribMulAction :
    DirectSum.GdistribMulAction (fun m : ℕ ↦ 𝒜 m) (degree 𝒜 ℳ) where
  smul_add := smul_add 𝒜 ℳ
  smul_zero := smul_zero 𝒜 ℳ

/-- The canonical graded-module structure on shifted associated-sheaf sections. -/
@[stacks 0B5R "canonical graded module on shifted associated-sheaf sections"]
noncomputable instance instGmodule :
    DirectSum.Gmodule (fun m : ℕ ↦ 𝒜 m) (degree 𝒜 ℳ) where
  add_smul := add_smul 𝒜 ℳ
  zero_smul := zero_smul 𝒜 ℳ

/-- The inferred dependent-index homogeneous action is the explicit global-sections map induced
by `actionMap`. The `GradedMonoid.GSMul.smul` projection is used because ordinary `HSMul`
notation does not track the output degree `(m : ℤ) + n`. -/
@[simp, stacks 0B5R "homogeneous action on shifted associated-sheaf sections"]
theorem smul_of {m : ℕ} {n : ℤ} (p : 𝒜 m) (x : degree 𝒜 ℳ n) :
    GradedMonoid.GSMul.smul
        (A := fun d : ℕ ↦ 𝒜 d) (M := degree 𝒜 ℳ) p x = smul 𝒜 ℳ p x := sorry

end AlgebraicGeometry.Proj.AssociatedModule.ShiftedSections
