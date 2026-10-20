module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic

/-!
# Two-periodic complexes from module endomorphisms

This file constructs the canonical two-periodic complex associated to two module
endomorphisms whose images lie in the opposite kernels.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The two module endomorphisms compose to zero in degree zero when the image of the
degree-zero map lies in the kernel of the degree-one map. -/
theorem ofModuleEnd_d₀_d₁ (phi psi : Module.End R M) (h₀₁ : phi.range ≤ psi.ker) :
    ModuleCat.ofHom phi ≫ ModuleCat.ofHom psi = 0 := sorry

/-- The two module endomorphisms compose to zero in degree one when the image of the
degree-one map lies in the kernel of the degree-zero map. -/
theorem ofModuleEnd_d₁_d₀ (phi psi : Module.End R M) (h₁₀ : psi.range ≤ phi.ker) :
    ModuleCat.ofHom psi ≫ ModuleCat.ofHom phi = 0 := sorry

/-- The two-periodic complex determined by two module endomorphisms whose images lie in
the opposite kernels. -/
def ofModuleEnd (phi psi : Module.End R M) (h₀₁ : phi.range ≤ psi.ker)
    (h₁₀ : psi.range ≤ phi.ker) : TwoPeriodicEndomorphism (ModuleCat R) where
  X := ModuleCat.of R M
  d₀ := ModuleCat.ofHom phi
  d₁ := ModuleCat.ofHom psi
  d₀_d₁ := ofModuleEnd_d₀_d₁ phi psi h₀₁
  d₁_d₀ := ofModuleEnd_d₁_d₀ phi psi h₁₀

/-- The carrier of `ofModuleEnd` is the original module. -/
@[simp]
theorem ofModuleEnd_X (phi psi : Module.End R M) (h₀₁ : phi.range ≤ psi.ker)
    (h₁₀ : psi.range ≤ phi.ker) :
    (ofModuleEnd phi psi h₀₁ h₁₀).X = ModuleCat.of R M := sorry

/-- The degree-zero differential of `ofModuleEnd` is its first endomorphism. -/
@[simp]
theorem ofModuleEnd_d₀ (phi psi : Module.End R M) (h₀₁ : phi.range ≤ psi.ker)
    (h₁₀ : psi.range ≤ phi.ker) :
    (ofModuleEnd phi psi h₀₁ h₁₀).d₀ = ModuleCat.ofHom phi := sorry

/-- The degree-one differential of `ofModuleEnd` is its second endomorphism. -/
@[simp]
theorem ofModuleEnd_d₁ (phi psi : Module.End R M) (h₀₁ : phi.range ≤ psi.ker)
    (h₁₀ : psi.range ≤ phi.ker) :
    (ofModuleEnd phi psi h₀₁ h₁₀).d₁ = ModuleCat.ofHom psi := sorry

/-- The complex `ofModuleEnd phi psi h₀₁ h₁₀` is acyclic exactly when each
image is the opposite kernel. -/
theorem ofModuleEnd_acyclic_iff (phi psi : Module.End R M)
    (h₀₁ : phi.range ≤ psi.ker) (h₁₀ : psi.range ≤ phi.ker) :
    (ofModuleEnd phi psi h₀₁ h₁₀).toCochainComplex.Acyclic ↔
      phi.range = psi.ker ∧ psi.range = phi.ker := sorry

end CategoryTheory.TwoPeriodicEndomorphism
