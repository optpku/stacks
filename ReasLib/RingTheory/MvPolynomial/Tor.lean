module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

noncomputable section

universe u

namespace MvPolynomial

/-- For the coefficient ring with polynomial action through `constantCoeff`, the inclusion
`idealOfVars σ A ^ (n + 1) ≤ idealOfVars σ A ^ n` induces the zero map on `Tor` in every
homological degree. -/
@[stacks 08RE]
theorem tor_map_pow_idealOfVars_eq_zero
    {A : Type u} [CommRing A] {σ : Type u} (i n : ℕ) :
    ((CategoryTheory.Tor (ModuleCat (MvPolynomial σ A)) i).obj
      ((ModuleCat.restrictScalars (MvPolynomial.constantCoeff : MvPolynomial σ A →+* A)).obj
        (ModuleCat.of A A))).map
      (ModuleCat.ofHom (Submodule.inclusion
        (Ideal.pow_le_pow_right (I := MvPolynomial.idealOfVars σ A) n.le_succ))) = 0 := sorry

end MvPolynomial
