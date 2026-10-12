/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.Int.Order.Units
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Module.Pi

@[expose] public section
universe u v
namespace AlgebraicGeometry.AlgebraicSpace
variable {G : Type u} [Group G] (χ : G →* ℤˣ)
variable {M : Type v} [AddCommGroup M]

/-- The semi-invariants of the regular permutation module, with inverse
pullback action. For finite G this is the local model of the torsor pushforward. -/
def regularCharacterInvariants : AddSubgroup (G → M) where
  carrier := {s | ∀ g h, s (g⁻¹ * h) = ((χ g : ℤˣ) : ℤ) • s h}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy g h
    simp only [Pi.add_apply, hx g h, hy g h]
    exact (zsmul_add _ _ _).symm
  neg_mem' := by
    intro x hx g h
    simp only [Pi.neg_apply, hx g h]
    exact (zsmul_neg _ _).symm

/-- The genuine character vector m ↦ (χ(g)m)g; no averaging or division. -/
def regularCharacterVector : M →+ regularCharacterInvariants (M := M) χ where
  toFun m := ⟨fun g ↦ ((χ g : ℤˣ) : ℤ) • m, by
    intro g h
    simp only [map_mul, map_inv, Int.units_inv_eq_self, Units.val_mul, mul_zsmul]⟩
  map_zero' := by ext g; simp
  map_add' := by
    intro x y
    apply Subtype.ext
    funext g
    exact zsmul_add _ _ _

/-- The inverse coordinate is evaluation at the identity of the torsor chart. -/
def regularCharacterEvaluation : regularCharacterInvariants (M := M) χ →+ M where
  toFun s := s.1 1
  map_zero' := rfl
  map_add' := fun _ _ ↦ rfl

/-- The identity coefficient of the character vector is the original element. -/
theorem regularCharacterEvaluation_vector (m : M) :
    regularCharacterEvaluation χ (regularCharacterVector χ m) = m := by
  simp [regularCharacterEvaluation, regularCharacterVector]

/-- Every semi-invariant is determined by its identity coefficient. -/
theorem regularCharacterVector_evaluation (s : regularCharacterInvariants (M := M) χ) :
    regularCharacterVector χ (regularCharacterEvaluation χ s) = s := by
  apply Subtype.ext
  funext h
  have hs := s.2 h⁻¹ 1
  simpa [regularCharacterVector, regularCharacterEvaluation, map_inv,
    Int.units_inv_eq_self] using hs.symm

/-- The local torsor character descent equivalence, valid also for torsion coefficients. -/
def regularCharacterEquiv : M ≃+ regularCharacterInvariants (M := M) χ where
  toFun := regularCharacterVector χ
  invFun := regularCharacterEvaluation χ
  left_inv := regularCharacterEvaluation_vector χ
  right_inv := regularCharacterVector_evaluation χ
  map_add' := (regularCharacterVector χ).map_add

end AlgebraicGeometry.AlgebraicSpace
