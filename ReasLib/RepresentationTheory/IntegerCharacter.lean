module

public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Int.Order.Units
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Endomorphism

/-! # Semi-invariants for integer-valued characters -/

@[expose] public section
open CategoryTheory
noncomputable section
universe u v
namespace IntegerCharacter

/-- The additive subgroup of `χ`-semi-invariants in an abelian group with `G`-action. -/
def invariantsAddSubgroup {G : Type u} [Group G] [Finite G]
    {A : AddCommGrpCat.{u + 1}} (σ : G →* Aut A) (χ : G →* ℤˣ) :
    AddSubgroup A where
  carrier := { a | ∀ g : G, (σ g).hom a = ((χ g : ℤˣ) : ℤ) • a }
  zero_mem' := by
    intro g
    simp only [map_zero, zsmul_zero]
  add_mem' := by
    intro a b ha hb g
    rw [map_add, ha g, hb g, zsmul_add]
  neg_mem' := by
    intro a ha g
    rw [map_neg, ha g, zsmul_neg]

/-- The `χ`-semi-invariants of an abelian group equipped with a `G`-action. -/
noncomputable def invariants {G : Type u} [Group G] [Finite G]
    {A : AddCommGrpCat.{u + 1}} (σ : G →* Aut A) (χ : G →* ℤˣ) :
    AddCommGrpCat.{u + 1} :=
  AddCommGrpCat.of (invariantsAddSubgroup σ χ)

/-- The inclusion of `χ`-semi-invariants into the ambient abelian group. -/
noncomputable def inclusion {G : Type u} [Group G] [Finite G]
    {A : AddCommGrpCat.{u + 1}} (σ : G →* Aut A) (χ : G →* ℤˣ) :
    invariants σ χ ⟶ A :=
  AddCommGrpCat.ofHom (invariantsAddSubgroup σ χ).subtype

/-- Membership in `invariants` is the sectionwise `χ`-transformation law. -/
theorem mem_invariants {G : Type u} [Group G] [Finite G]
    {A : AddCommGrpCat.{u + 1}} (σ : G →* Aut A) (χ : G →* ℤˣ) (a : A) :
    a ∈ invariantsAddSubgroup σ χ ↔
      ∀ g : G, (σ g).hom a = ((χ g : ℤˣ) : ℤ) • a := Iff.rfl

/-- A G-equivariant morphism of ambient abelian groups induces a morphism of
`χ`-semi-invariants. -/
noncomputable def map {G : Type u} [Group G] [Finite G]
    {A B : AddCommGrpCat.{u + 1}} {σA : G →* Aut A} {σB : G →* Aut B}
    (χ : G →* ℤˣ) (ψ : A ⟶ B)
    (h_equivariant : ∀ g : G, (σA g).hom ≫ ψ = ψ ≫ (σB g).hom) :
    invariants σA χ ⟶ invariants σB χ :=
  AddCommGrpCat.ofHom
    { toFun := fun a ↦ ⟨ψ (a : A), sorry⟩
      map_zero' := sorry
      map_add' := sorry }

/-- The `χ`-semi-invariant map intertwines the subtype inclusions. -/
theorem map_inclusion {G : Type u} [Group G] [Finite G]
    {A B : AddCommGrpCat.{u + 1}} {σA : G →* Aut A} {σB : G →* Aut B}
    (χ : G →* ℤˣ) (ψ : A ⟶ B)
    (h_equivariant : ∀ g : G, (σA g).hom ≫ ψ = ψ ≫ (σB g).hom) :
    inclusion σA χ ≫ ψ =
      map χ ψ h_equivariant ≫ inclusion σB χ :=
  sorry

section Regular
variable {G : Type u} [Group G] (χ : G →* ℤˣ)
variable {M : Type v} [AddCommGroup M]

/-- The semi-invariants of the regular permutation module, with inverse
pullback action. For finite G this is the local model of the torsor pushforward. -/
def regularInvariants : AddSubgroup (G → M) where
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
def regularVector : M →+ regularInvariants (M := M) χ where
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
def regularEvaluation : regularInvariants (M := M) χ →+ M where
  toFun s := s.1 1
  map_zero' := rfl
  map_add' := fun _ _ ↦ rfl

/-- The identity coefficient of the character vector is the original element. -/
theorem regularEvaluation_vector (m : M) :
    regularEvaluation χ (regularVector χ m) = m := by
  simp [regularEvaluation, regularVector]

/-- Every semi-invariant is determined by its identity coefficient. -/
theorem regularVector_evaluation (s : regularInvariants (M := M) χ) :
    regularVector χ (regularEvaluation χ s) = s := by
  apply Subtype.ext
  funext h
  have hs := s.2 h⁻¹ 1
  simpa [regularVector, regularEvaluation, map_inv,
    Int.units_inv_eq_self] using hs.symm

/-- The local torsor character descent equivalence, valid also for torsion coefficients. -/
def regularEquiv : M ≃+ regularInvariants (M := M) χ where
  toFun := regularVector χ
  invFun := regularEvaluation χ
  left_inv := regularEvaluation_vector χ
  right_inv := regularVector_evaluation χ
  map_add' := (regularVector χ).map_add

end Regular
end IntegerCharacter
