/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat}

/-- For a quasi-coherent module on an affine scheme, vanishing after restriction to
the basic open defined by a global section makes every global section torsion for
the corresponding scalar action. -/
theorem exists_pow_smul_eq_zero_of_isZero_restrict
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    (f : Γ(Spec R, ⊤))
    (hM : IsZero (M.restrict ((Spec R).basicOpen f).ι)) :
    ∀ s : Γ(M, ⊤), ∃ n : ℕ, f ^ n • s = 0 := sorry

end AlgebraicGeometry.Scheme.Modules
