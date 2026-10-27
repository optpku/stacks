/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.DifferentialOperator
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.CommRing
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Differential operators between module presheaves

Differential operators between module presheaves are defined objectwise using
the bundled `ModuleCat` predicate.  This is the functor-category layer shared by
presheaf constructions and by module sheafification.
-/

@[expose] public section

open CategoryTheory

universe u v w z

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C]
variable {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{w}}
variable (φ : O₁ ⟶ O₂)
variable {F G H : PresheafOfModules.{z} (ringPresheaf O₂)}

/-- A morphism between scalar-restricted module presheaves has
differential-operator order at most `k` when every objectwise bundled module
map has that order. -/
@[stacks 09CR "presheaf differential operators"]
def IsDifferentialOperatorOfOrder
    (D : (restrictScalars (presheafStructureMap φ)).obj F ⟶
      (restrictScalars (presheafStructureMap φ)).obj G)
    (k : ℕ) : Prop :=
  ∀ X : Cᵒᵖ, ModuleCat.IsDifferentialOperatorOfOrder (φ.app X).hom (D.app X) k

namespace IsDifferentialOperatorOfOrder

-- The module-level closure lemmas are still unproved.  These private proofs use only
-- the recursive predicate, so the presheaf results do not inherit that proof debt.
section LinearMapProofs

variable {R S L M N : Type*} [Semiring R]
variable [AddCommGroup L] [Module R L] [DistribSMul S L] [SMulCommClass S R L]
variable [AddCommGroup M] [Module R M] [DistribSMul S M] [SMulCommClass S R M]
variable [AddCommGroup N] [Module R N] [DistribSMul S N] [SMulCommClass S R N]

private theorem linear_zero (k : ℕ) :
    (0 : M →ₗ[R] N).IsDifferentialOperatorOfOrder S k := by
  induction k with
  | zero =>
    intro s
    simp only [LinearMap.scalarCommutator, LinearMap.zero_comp, LinearMap.comp_zero, sub_self]
  | succ k ih =>
    intro s
    simpa only [LinearMap.scalarCommutator, LinearMap.zero_comp, LinearMap.comp_zero,
      sub_self] using ih

private theorem linear_commutator_add (D E : M →ₗ[R] N) (s : S) :
    (D + E).scalarCommutator s = D.scalarCommutator s + E.scalarCommutator s := by
  simp only [LinearMap.scalarCommutator, LinearMap.add_comp, LinearMap.comp_add]
  exact add_sub_add_comm _ _ _ _

private theorem linear_add {D E : M →ₗ[R] N} {k : ℕ}
    (hD : D.IsDifferentialOperatorOfOrder S k)
    (hE : E.IsDifferentialOperatorOfOrder S k) :
    (D + E).IsDifferentialOperatorOfOrder S k := by
  induction k generalizing D E with
  | zero =>
    intro s
    rw [linear_commutator_add, hD s, hE s, add_zero]
  | succ k ih =>
    intro s
    rw [linear_commutator_add]
    exact ih (hD s) (hE s)

private theorem linear_commutator_neg (D : M →ₗ[R] N) (s : S) :
    (-D).scalarCommutator s = -D.scalarCommutator s := by
  simp only [LinearMap.scalarCommutator, LinearMap.neg_comp, LinearMap.comp_neg,
    neg_sub_neg, neg_sub]

private theorem linear_neg {D : M →ₗ[R] N} {k : ℕ}
    (hD : D.IsDifferentialOperatorOfOrder S k) :
    (-D).IsDifferentialOperatorOfOrder S k := by
  induction k generalizing D with
  | zero =>
    intro s
    rw [linear_commutator_neg, hD s, neg_zero]
  | succ k ih =>
    intro s
    rw [linear_commutator_neg]
    exact ih (hD s)

private theorem linear_commutator_comp (D : L →ₗ[R] M) (E : M →ₗ[R] N) (s : S) :
    (E.comp D).scalarCommutator s =
      E.comp (D.scalarCommutator s) + (E.scalarCommutator s).comp D := by
  simp only [LinearMap.scalarCommutator, LinearMap.comp_sub, LinearMap.sub_comp,
    LinearMap.comp_assoc]
  exact (sub_add_sub_cancel _ _ _).symm

private theorem linear_comp {D : L →ₗ[R] M} {E : M →ₗ[R] N} {k l : ℕ}
    (hD : D.IsDifferentialOperatorOfOrder S k)
    (hE : E.IsDifferentialOperatorOfOrder S l) :
    (E.comp D).IsDifferentialOperatorOfOrder S (k + l) := by
  induction k generalizing D E l with
  | zero =>
    induction l generalizing E with
    | zero =>
      intro s
      rw [linear_commutator_comp, hD s, hE s, LinearMap.comp_zero,
        LinearMap.zero_comp, add_zero]
    | succ l ih =>
      intro s
      rw [linear_commutator_comp, hD s, LinearMap.comp_zero, zero_add]
      exact ih (hE s)
  | succ k ih =>
    induction l generalizing E with
    | zero =>
      intro s
      rw [linear_commutator_comp, hE s, LinearMap.zero_comp, add_zero]
      exact ih (hD s) hE
    | succ l ih' =>
      change ∀ s : S, ((E.comp D).scalarCommutator s).IsDifferentialOperatorOfOrder S
        ((k + 1) + l)
      intro s
      rw [linear_commutator_comp]
      apply linear_add
      · show (E.comp (D.scalarCommutator s)).IsDifferentialOperatorOfOrder S ((k + 1) + l)
        simpa only [Nat.succ_add, Nat.add_succ] using ih (hD s) hE
      · show ((E.scalarCommutator s).comp D).IsDifferentialOperatorOfOrder S ((k + 1) + l)
        exact ih' (hE s)

private theorem linear_le_succ {D : M →ₗ[R] N} {k : ℕ}
    (hD : D.IsDifferentialOperatorOfOrder S k) :
    D.IsDifferentialOperatorOfOrder S (k + 1) := by
  induction k generalizing D with
  | zero =>
    intro s
    rw [hD s]
    exact linear_zero 0
  | succ k ih =>
    intro s
    exact ih (hD s)

end LinearMapProofs

section ModuleCatProofs

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
variable {L M N : ModuleCat S}

private theorem module_comp
    {D : (ModuleCat.restrictScalars f).obj L ⟶ (ModuleCat.restrictScalars f).obj M}
    {E : (ModuleCat.restrictScalars f).obj M ⟶ (ModuleCat.restrictScalars f).obj N}
    {k l : ℕ} (hD : ModuleCat.IsDifferentialOperatorOfOrder f D k)
    (hE : ModuleCat.IsDifferentialOperatorOfOrder f E l) :
    ModuleCat.IsDifferentialOperatorOfOrder f (D ≫ E) (k + l) := by
  -- Pin the retained actions on all three restricted modules, including the middle one.
  exact @linear_comp R S
    ((ModuleCat.restrictScalars f).obj L) ((ModuleCat.restrictScalars f).obj M)
    ((ModuleCat.restrictScalars f).obj N)
    _ _ _ _ (ModuleCat.RestrictScalars.smulCommClass f L)
    _ _ _ (ModuleCat.RestrictScalars.smulCommClass f M)
    _ _ _ (ModuleCat.RestrictScalars.smulCommClass f N) D.hom E.hom k l hD hE

private theorem module_restrict_map (g : M ⟶ N) :
    ModuleCat.IsDifferentialOperatorOfOrder f ((ModuleCat.restrictScalars f).map g) 0 := by
  intro s
  apply LinearMap.ext
  intro m
  change g.hom (s • m) - s • g.hom m = 0
  exact sub_eq_zero.mpr (g.hom.map_smul s m)

end ModuleCatProofs

/-- Evaluate a presheaf differential operator at an object. -/
theorem app
    (D : (restrictScalars (presheafStructureMap φ)).obj F ⟶
      (restrictScalars (presheafStructureMap φ)).obj G)
    {k : ℕ} (hD : IsDifferentialOperatorOfOrder φ D k) (X : Cᵒᵖ) :
    ModuleCat.IsDifferentialOperatorOfOrder (φ.app X).hom (D.app X) k :=
  hD X

/-- The zero morphism of restricted module presheaves has every
differential-operator order bound. -/
theorem zero (k : ℕ) :
    IsDifferentialOperatorOfOrder φ
      (0 : (restrictScalars (presheafStructureMap φ)).obj F ⟶
        (restrictScalars (presheafStructureMap φ)).obj G) k := by
  intro X
  exact linear_zero k

/-- The sum of two presheaf differential operators with a common bound has the
same bound. -/
theorem add
    {D E : (restrictScalars (presheafStructureMap φ)).obj F ⟶
      (restrictScalars (presheafStructureMap φ)).obj G}
    {k : ℕ} (hD : IsDifferentialOperatorOfOrder φ D k)
    (hE : IsDifferentialOperatorOfOrder φ E k) :
    IsDifferentialOperatorOfOrder φ (D + E) k := by
  intro X
  exact linear_add (hD X) (hE X)

/-- Negation preserves the presheaf differential-operator order bound. -/
theorem neg
    {D : (restrictScalars (presheafStructureMap φ)).obj F ⟶
      (restrictScalars (presheafStructureMap φ)).obj G}
    {k : ℕ} (hD : IsDifferentialOperatorOfOrder φ D k) :
    IsDifferentialOperatorOfOrder φ (-D) k := by
  intro X
  exact linear_neg (hD X)

/-- The identity morphism is a presheaf differential operator of order zero. -/
theorem id :
    IsDifferentialOperatorOfOrder φ
      (𝟙 ((restrictScalars (presheafStructureMap φ)).obj F)) 0 := by
  intro X s
  apply LinearMap.ext
  intro m
  change s • m - s • m = 0
  exact sub_self _

/-- Composing presheaf differential operators adds their order bounds. -/
@[stacks 09CS "composition of presheaf differential operators"]
theorem comp
    {D : (restrictScalars (presheafStructureMap φ)).obj F ⟶
      (restrictScalars (presheafStructureMap φ)).obj G}
    {E : (restrictScalars (presheafStructureMap φ)).obj G ⟶
      (restrictScalars (presheafStructureMap φ)).obj H}
    {k l : ℕ} (hD : IsDifferentialOperatorOfOrder φ D k)
    (hE : IsDifferentialOperatorOfOrder φ E l) :
    IsDifferentialOperatorOfOrder φ (D ≫ E) (k + l) := by
  intro X
  exact module_comp (φ.app X).hom (hD X) (hE X)

/-- A presheaf differential operator has the successor order bound. -/
theorem le_succ
    {D : (restrictScalars (presheafStructureMap φ)).obj F ⟶
      (restrictScalars (presheafStructureMap φ)).obj G}
    {k : ℕ} (hD : IsDifferentialOperatorOfOrder φ D k) :
    IsDifferentialOperatorOfOrder φ D (k + 1) := by
  intro X
  exact linear_le_succ (hD X)

/-- A presheaf differential operator has every larger order bound. -/
theorem mono
    {D : (restrictScalars (presheafStructureMap φ)).obj F ⟶
      (restrictScalars (presheafStructureMap φ)).obj G}
    {k l : ℕ} (hD : IsDifferentialOperatorOfOrder φ D k) (hkl : k ≤ l) :
    IsDifferentialOperatorOfOrder φ D l := by
  induction hkl with
  | refl => exact hD
  | @step l hkl ih => exact le_succ φ ih

/-- Precomposition with an `O₂`-linear presheaf morphism preserves a differential-operator
order bound. -/
theorem precompose
    {F' : PresheafOfModules.{z} (ringPresheaf O₂)} (g : F' ⟶ F)
    {D : (restrictScalars (presheafStructureMap φ)).obj F ⟶
      (restrictScalars (presheafStructureMap φ)).obj G}
    {k : ℕ} (hD : IsDifferentialOperatorOfOrder φ D k) :
    IsDifferentialOperatorOfOrder φ
      ((restrictScalars (presheafStructureMap φ)).map g ≫ D) k := by
  intro X
  exact (Nat.zero_add k) ▸
    module_comp (φ.app X).hom (module_restrict_map (φ.app X).hom (g.app X)) (hD X)

/-- Postcomposition with an `O₂`-linear presheaf morphism preserves a differential-operator
order bound. -/
theorem postcompose
    {G' : PresheafOfModules.{z} (ringPresheaf O₂)}
    {D : (restrictScalars (presheafStructureMap φ)).obj F ⟶
      (restrictScalars (presheafStructureMap φ)).obj G}
    {k : ℕ} (hD : IsDifferentialOperatorOfOrder φ D k) (g : G ⟶ G') :
    IsDifferentialOperatorOfOrder φ
      (D ≫ (restrictScalars (presheafStructureMap φ)).map g) k := by
  intro X
  exact module_comp (φ.app X).hom (hD X) (module_restrict_map (φ.app X).hom (g.app X))

end IsDifferentialOperatorOfOrder

end PresheafOfModules
