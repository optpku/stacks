/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Basic
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Differential Graded Categories

This leaf owns the small, enrichment-level core of differential graded categories: graded
hom modules, their differential, and signed composition.  It intentionally does not construct
the degree-zero category, the category of closed morphisms, or a homotopy category.

It is deliberately distinct from `CategoryTheory.GradedCategory`, which starts from an ordinary
preadditive category together with a direct-sum decomposition of total hom modules.  Such a
total category is not part of the present enrichment-level data.
-/

@[expose] public section

universe u v w

/-- Transport a term along an equality of indices.  This is retained at its historical root
namespace because it is the common dependent transport used by the differential graded category
API. -/
def castHom {α : Sort _} {β : α → Sort _} {a b : α} (h : a = b) : β a → β b :=
  fun x ↦ Eq.ndrec x h

namespace DifferentialGradedCategory

/-- Arithmetic identity used to align the left Leibniz term in degree `(i, j)`. -/
theorem d_comp_left_index (i j : ℤ) : i + (j + 1) = i + j + 1 := sorry

/-- Arithmetic identity used to align the right Leibniz term in degree `(i, j)`. -/
theorem d_comp_right_index (i j : ℤ) : (i + 1) + j = i + j + 1 := sorry

/-- Arithmetic identity used to align the first Leibniz term in degree `(0, 0)`. -/
theorem zero_add_zero_succ_eq : 0 + (0 + 1 : ℤ) = 0 + 1 := sorry

/-- Arithmetic identity used to align the second Leibniz term in degree `(0, 0)`. -/
theorem zero_succ_add_zero_eq : (0 + 1 : ℤ) + 0 = 0 + 1 := sorry

/-- Arithmetic identity used to align the first Leibniz term in degree `(0, -1)`. -/
theorem negOne_add_zero_succ_eq_zero : -1 + (0 + 1 : ℤ) = 0 := sorry

/-- Arithmetic identity used to align the second Leibniz term in degree `(0, -1)`. -/
theorem negOne_succ_add_zero_eq_zero : (-1 + 1 : ℤ) + 0 = 0 := sorry

/-- Arithmetic identity used to align the first Leibniz term in degree `(-1, 0)`. -/
theorem zero_add_negOne_succ_eq_zero : 0 + (-1 + 1 : ℤ) = 0 := sorry

/-- Arithmetic identity used to align the second Leibniz term in degree `(-1, 0)`. -/
theorem zero_succ_add_negOne_eq_zero : (0 + 1 : ℤ) + -1 = 0 := sorry

/-- Arithmetic identity used to align the first homotopy-composition term in degree `-1`. -/
theorem zero_add_negOne_eq : 0 + (-1 : ℤ) = -1 := sorry

/-- Arithmetic identity used to align the second homotopy-composition term in degree `-1`. -/
theorem negOne_add_zero_eq : (-1 : ℤ) + 0 = -1 := sorry

end DifferentialGradedCategory

open DifferentialGradedCategory

/-- Definition 22.26.1 (Tag `09L5`): a differential graded category over `R`, encoded by graded
`R`-modules of morphisms together with differentials, identities, and graded composition.

This is the reusable enrichment-level owner.  Categories of closed degree-zero morphisms and
their homotopy quotients belong in separate layers. -/
@[stacks 09L5]
class DifferentialGradedCategory (R : outParam (Type u)) [CommRing R] (C : Type v) where
  /-- The degree-`n` homogeneous morphisms from `X` to `Y`. -/
  Hom : C → C → ℤ → Type w
  /-- The additive commutative group structure on each homogeneous hom module. -/
  homAddCommGroup (X Y : C) (n : ℤ) : AddCommGroup (Hom X Y n)
  /-- The `R`-module structure on each homogeneous hom module. -/
  homModule (X Y : C) (n : ℤ) : Module R (Hom X Y n)
  /-- The degree-`1` differential on homogeneous morphisms. -/
  d {X Y : C} (n : ℤ) : Hom X Y n → Hom X Y (n + 1)
  /-- The identity homogeneous morphism, in degree zero. -/
  id (X : C) : Hom X X 0
  /-- Homogeneous composition, which adds degrees. -/
  comp {X Y Z : C} {i j : ℤ} : Hom Y Z j → Hom X Y i → Hom X Z (i + j)
  /-- The differential squares to zero. -/
  d_sq {X Y : C} (n : ℤ) (f : Hom X Y n) : d (n + 1) (d n f) = 0
  /-- Identities are closed. -/
  d_id (X : C) : d 0 (id X) = 0
  /-- Left identity after the necessary degree transport. -/
  id_comp_hom {X Y : C} {i : ℤ} (f : Hom X Y i) :
    castHom (add_zero i) (comp (id Y) f) = f
  /-- Right identity after the necessary degree transport. -/
  comp_id_hom {X Y : C} {i : ℤ} (f : Hom X Y i) :
    castHom (zero_add i) (comp f (id X)) = f
  /-- Associativity after the necessary degree transport. -/
  comp_assoc {W X Y Z : C} {i j k : ℤ} (h : Hom Y Z k) (g : Hom X Y j) (f : Hom W X i) :
    castHom (add_assoc i j k) (comp h (comp g f)) = comp (comp h g) f
  /-- Composition is additive in its left input. -/
  comp_add_left {X Y Z : C} {i j : ℤ} (g₁ g₂ : Hom Y Z j) (f : Hom X Y i) :
    comp (g₁ + g₂) f = comp g₁ f + comp g₂ f
  /-- Composition is additive in its right input. -/
  comp_add_right {X Y Z : C} {i j : ℤ} (g : Hom Y Z j) (f₁ f₂ : Hom X Y i) :
    comp g (f₁ + f₂) = comp g f₁ + comp g f₂
  /-- Composition is `R`-linear in its left input. -/
  comp_smul_left {X Y Z : C} {i j : ℤ} (r : R) (g : Hom Y Z j) (f : Hom X Y i) :
    comp (r • g) f = r • comp g f
  /-- Composition is `R`-linear in its right input. -/
  comp_smul_right {X Y Z : C} {i j : ℤ} (r : R) (g : Hom Y Z j) (f : Hom X Y i) :
    comp g (r • f) = r • comp g f
  /-- The differential is additive. -/
  d_add {X Y : C} (n : ℤ) (f g : Hom X Y n) : d n (f + g) = d n f + d n g
  /-- The differential is `R`-linear. -/
  d_smul {X Y : C} (n : ℤ) (r : R) (f : Hom X Y n) : d n (r • f) = r • d n f
  /-- The signed graded Leibniz rule. -/
  d_comp {X Y Z : C} {i j : ℤ} (g : Hom Y Z j) (f : Hom X Y i) :
    d (i + j) (comp g f) =
      castHom (d_comp_left_index i j) (comp (d j g) f) +
        (j.negOnePow : R) • castHom (d_comp_right_index i j) (comp g (d i f))

attribute [reducible, instance] DifferentialGradedCategory.homAddCommGroup
attribute [reducible, instance] DifferentialGradedCategory.homModule

namespace DifferentialGradedCategory

/-- Notation for homogeneous morphisms in a differential graded category. -/
scoped notation:max X " ⟶[" n "] " Y =>
  DifferentialGradedCategory.Hom X Y n

/-- Dependent transport preserves addition. -/
@[simp]
theorem castHom_add {α : Sort _} {β : α → Type _} [∀ a, Add (β a)]
    {a b : α} (h : a = b) (x y : β a) :
    castHom h (x + y) = castHom h x + castHom h y := sorry

/-- Dependent transport commutes with scalar multiplication. -/
@[simp]
theorem castHom_smul {S : Type _} {α : Sort _} {β : α → Type _}
    [∀ a, SMul S (β a)] {a b : α} (h : a = b) (r : S) (x : β a) :
    castHom h (r • x) = r • castHom h x := sorry

variable {R : Type u} [CommRing R]
variable {C : Type v} [D : DifferentialGradedCategory R C]

open scoped DifferentialGradedCategory

/-- Transport along reflexivity is the identity. -/
@[simp]
theorem castHom_rfl {α : Sort _} {β : α → Sort _} {a : α} (x : β a) :
    castHom rfl x = x := sorry

/-- Dependent transport sends zero to zero. -/
@[simp]
theorem castHom_zero {α : Sort _} {β : α → Type _} [∀ a, Zero (β a)]
    {a b : α} (h : a = b) :
    castHom h (0 : β a) = 0 := sorry

/-- Transporting along an equality and then its inverse is the identity. -/
@[simp]
theorem castHom_symm_castHom {α : Sort _} {β : α → Sort _} {a b : α}
    (h : a = b) (x : β a) :
    castHom h.symm (castHom h x) = x := sorry

/-- The standard dependent `cast` agrees with `castHom`. -/
theorem cast_eq_castHom {α : Sort _} {β : α → Type _} {a b : α}
    (h : a = b) (x : β a) :
    cast (congrArg β h) x = castHom h x := sorry

/-- Successive dependent transports compose. -/
theorem castHom_trans {α : Sort _} {β : α → Sort _} {a b c : α}
    (h₁ : a = b) (h₂ : b = c) (x : β a) :
    castHom h₂ (castHom h₁ x) = castHom (h₁.trans h₂) x := sorry

/-- The transported term does not depend on the chosen proof of equality. -/
theorem castHom_congr {α : Sort _} {β : α → Sort _} {a b : α}
    (h₁ h₂ : a = b) (x : β a) :
    castHom h₁ x = castHom h₂ x := sorry

/-- The differential commutes with transport of a homogeneous degree. -/
@[simp]
theorem d_castHom {X Y : C} {i j : ℤ} (h : i = j) (f : X ⟶[i] Y) :
    D.d j (castHom h f) = castHom (congrArg (fun n : ℤ ↦ n + 1) h) (D.d i f) := sorry

/-- Right composition commutes with transport of the degree of its right input. -/
theorem comp_castHom_right {X Y Z : C} {i i' j : ℤ}
    (h : i = i') (g : Y ⟶[j] Z) (f : X ⟶[i] Y) :
    castHom (congrArg (fun n : ℤ ↦ n + j) h) (D.comp g f) = D.comp g (castHom h f) := sorry

/-- Left composition commutes with transport of the degree of its left input. -/
theorem comp_castHom_left {X Y Z : C} {i j j' : ℤ}
    (h : j = j') (g : Y ⟶[j] Z) (f : X ⟶[i] Y) :
    castHom (congrArg (fun n : ℤ ↦ i + n) h) (D.comp g f) = D.comp (castHom h g) f := sorry

/-- Left identity for closed degree-zero morphisms. -/
theorem id_comp {X Y : C} (f : X ⟶[0] Y) : D.comp (D.id Y) f = f := sorry

/-- Right identity for closed degree-zero morphisms. -/
theorem comp_id {X Y : C} (f : X ⟶[0] Y) : D.comp f (D.id X) = f := sorry

/-- Associativity of degree-zero composition. -/
theorem comp_assoc_zero {W X Y Z : C} (h : Y ⟶[0] Z) (g : X ⟶[0] Y) (f : W ⟶[0] X) :
    D.comp h (D.comp g f) = D.comp (D.comp h g) f := sorry

/-- The Leibniz rule for two degree-zero morphisms. -/
theorem d_comp_zero_zero {X Y Z : C} (g : Y ⟶[0] Z) (f : X ⟶[0] Y) :
    D.d 0 (D.comp g f) =
      castHom zero_add_zero_succ_eq (D.comp (D.d 0 g) f) +
        castHom zero_succ_add_zero_eq (D.comp g (D.d 0 f)) := sorry

/-- The Leibniz rule for a degree-zero morphism after a degree-`-1` morphism. -/
theorem d_comp_zero_negOne {X Y Z : C} (g : Y ⟶[0] Z) (f : X ⟶[-1] Y) :
    D.d (-1) (D.comp g f) =
      castHom negOne_add_zero_succ_eq_zero (D.comp (D.d 0 g) f) +
        castHom negOne_succ_add_zero_eq_zero (D.comp g (D.d (-1) f)) := sorry

/-- The Leibniz rule for a degree-`-1` morphism after a degree-zero morphism. -/
theorem d_comp_negOne_zero {X Y Z : C} (g : Y ⟶[-1] Z) (f : X ⟶[0] Y) :
    D.d (-1) (D.comp g f) =
      castHom zero_add_negOne_succ_eq_zero (D.comp (D.d (-1) g) f) -
        castHom zero_succ_add_negOne_eq_zero (D.comp g (D.d 0 f)) := sorry

/-- The differential sends the zero homogeneous morphism to zero. -/
@[simp]
theorem d_zero {X Y : C} (n : ℤ) : D.d n (0 : X ⟶[n] Y) = 0 := sorry

/-- The differential commutes with additive inverses. -/
theorem d_neg {X Y : C} (n : ℤ) (f : X ⟶[n] Y) : D.d n (-f) = -D.d n f := sorry

/-- The differential commutes with subtraction. -/
theorem d_sub {X Y : C} (n : ℤ) (f g : X ⟶[n] Y) :
    D.d n (f - g) = D.d n f - D.d n g := sorry

/-- Left composition by zero vanishes. -/
@[simp]
theorem comp_zero_left {X Y Z : C} {i j : ℤ} (f : X ⟶[i] Y) :
    D.comp (0 : Y ⟶[j] Z) f = 0 := sorry

/-- Right composition by zero vanishes. -/
@[simp]
theorem comp_zero_right {X Y Z : C} {i j : ℤ} (g : Y ⟶[j] Z) :
    D.comp g (0 : X ⟶[i] Y) = 0 := sorry

/-- Left composition commutes with additive inverses. -/
theorem comp_neg_left {X Y Z : C} {i j : ℤ} (g : Y ⟶[j] Z) (f : X ⟶[i] Y) :
    D.comp (-g) f = -D.comp g f := sorry

/-- Right composition commutes with additive inverses. -/
theorem comp_neg_right {X Y Z : C} {i j : ℤ} (g : Y ⟶[j] Z) (f : X ⟶[i] Y) :
    D.comp g (-f) = -D.comp g f := sorry

/-- Left composition commutes with subtraction. -/
theorem comp_sub_left {X Y Z : C} {i j : ℤ} (g₁ g₂ : Y ⟶[j] Z) (f : X ⟶[i] Y) :
    D.comp (g₁ - g₂) f = D.comp g₁ f - D.comp g₂ f := sorry

/-- Right composition commutes with subtraction. -/
theorem comp_sub_right {X Y Z : C} {i j : ℤ} (g : Y ⟶[j] Z) (f₁ f₂ : X ⟶[i] Y) :
    D.comp g (f₁ - f₂) = D.comp g f₁ - D.comp g f₂ := sorry

end DifferentialGradedCategory
