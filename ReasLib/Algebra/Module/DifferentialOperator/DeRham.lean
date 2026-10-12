/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.DifferentialOperator.Basic
public import ReasLib.LinearAlgebra.ExteriorPower.Forms
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Exterior-Power de Rham Differential Families

This leaf owns the algebraic data shared by de Rham constructions built from
an arbitrary derivation.  It separates the de Rham formulas from the
square-zero condition, so results such as the first-order bound can depend on
only the hypotheses they actually use.

@stack 0G34
@stack 07HY
@stack 0FKG
-/

@[expose] public section

universe u v

namespace DifferentialOperator.DeRham

section

variable {R : Type u} {S : Type v} {M : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

/-- A family of degree-raising `R`-linear maps on the exterior-power terms of an `S`-module. -/
@[stacks 0G34]
abbrev Family
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (M : Type v) [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M] :=
  ∀ p : ℕ, exteriorPower.form.Hom R S M M p (p + 1)

variable {N : Type v}
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/-- A degreewise map of exterior-power terms intertwines two differential families. -/
@[stacks 07HY]
def Descends (f : M →ₗ[S] N) (δM : Family R S M) (δN : Family R S N) : Prop :=
  ∀ p : ℕ,
    (δN p).comp (exteriorPower.form.mapRestrictScalars R f p) =
      (exteriorPower.form.mapRestrictScalars R f (p + 1)).comp (δM p)

/-- A differential family maps the kernel of every component of an induced exterior-form map
into the kernel in the next degree. -/
@[stacks 07HY]
def PreservesKernel (f : M →ₗ[S] N) (δ : Family R S M) : Prop :=
  ∀ p : ℕ,
    exteriorPower.form.ker (exteriorPower.form.mapRestrictScalars R f p) ≤
      exteriorPower.form.ker
        ((exteriorPower.form.mapRestrictScalars R f (p + 1)).comp (δ p))

/-- The exact `p`-form `D b₁ ∧ ... ∧ D bₚ` associated to a derivation.  In degree zero this is
the unit of `S`. -/
@[stacks 0FKG]
def exactForm (D : Derivation R S M) :
    (p : ℕ) → (Fin p → S) → exteriorPower.form S M p
  | 0 => fun _ ↦ (1 : S)
  | 1 => fun b ↦ D (b 0)
  | p + 2 => fun b ↦ exteriorPower.ιMulti S (p + 2) fun i ↦ D (b i)

/-- The basic `p`-form `b₀ D b₁ ∧ ... ∧ D bₚ` associated to a derivation. -/
@[stacks 0FKG]
def basicForm (D : Derivation R S M) (p : ℕ) (b₀ : S) (b : Fin p → S) :
    exteriorPower.form S M p :=
  b₀ • exactForm D p b

/-- The single degree-uniform formula satisfied by a de Rham family extending a derivation. -/
@[stacks 0G34]
structure SatisfiesFormula (D : Derivation R S M) (δ : Family R S M) :
    Prop where
  /-- The differential sends `b₀ D b₁ ∧ ... ∧ D bₚ` to
  `D b₀ ∧ D b₁ ∧ ... ∧ D bₚ` in every degree. -/
  basic (p : ℕ) (b₀ : S) (b : Fin p → S) :
    δ p (basicForm D p b₀ b) = exactForm D (p + 1) (Fin.cons b₀ b)

/-- Construct a de Rham formula witness from its defining basic-form identity. -/
def SatisfiesFormula.ofBasic {D : Derivation R S M} {δ : Family R S M}
    (hbasic : ∀ (p : ℕ) (b₀ : S) (b : Fin p → S),
      δ p (basicForm D p b₀ b) = exactForm D (p + 1) (Fin.cons b₀ b)) :
    SatisfiesFormula D δ :=
  { basic := hbasic }

namespace SatisfiesFormula

/-- The degree-zero differential of a family satisfying the de Rham formula is the derivation. -/
theorem degree_zero {D : Derivation R S M} {δ : Family R S M}
    (hδ : SatisfiesFormula D δ) :
    δ 0 = D.toLinearMap := sorry

/-- The degree-one specialization of the uniform basic-form rule. -/
theorem degree_one {D : Derivation R S M} {δ : Family R S M}
    (hδ : SatisfiesFormula D δ) (f₀ f₁ : S) :
    δ 1 (f₀ • D f₁) =
      exteriorPower.ιMulti S 2 (Fin.cases (D f₀) fun _ ↦ D f₁) := sorry

/-- The positive higher-degree specialization of the uniform basic-form rule. -/
theorem higher {D : Derivation R S M} {δ : Family R S M}
    (hδ : SatisfiesFormula D δ) (p : ℕ) (f₀ : S) (fs : Fin (p + 2) → S) :
    δ (p + 2) (f₀ • exteriorPower.ιMulti S (p + 2) (fun i ↦ D (fs i))) =
      exteriorPower.ιMulti S (p + 3) (Fin.cases (D f₀) fun i ↦ D (fs i)) := sorry

end SatisfiesFormula

/-- Consecutive maps in a degree-raising exterior-power family compose to zero. -/
@[stacks 0G34]
def SquaresToZero (δ : Family R S M) : Prop :=
  ∀ p : ℕ, (δ (p + 1)).comp (δ p) = 0

/-- A de Rham differential family is a family satisfying the exterior-power formulas and the
square-zero relation. -/
@[stacks 0G34]
structure IsDifferential (D : Derivation R S M) (δ : Family R S M) : Prop where
  /-- The family satisfies the degreewise exterior-power de Rham formulas. -/
  formula : SatisfiesFormula D δ
  /-- The family is a differential: consecutive maps compose to zero. -/
  square_zero : SquaresToZero δ

/-- Construct a differential witness from the de Rham formula and square-zero conditions. -/
def IsDifferential.ofFormula {D : Derivation R S M} {δ : Family R S M}
    (hformula : SatisfiesFormula D δ) (hsquare_zero : SquaresToZero δ) :
    IsDifferential D δ :=
  { formula := hformula
    square_zero := hsquare_zero }

/-- The differential predicate is equivalent to its formula and square-zero conditions. -/
theorem isDifferential_iff {D : Derivation R S M} {δ : Family R S M} :
    IsDifferential D δ ↔ SatisfiesFormula D δ ∧ SquaresToZero δ := sorry

/-- The degree-`p` map of an exterior-power family is an order-one differential operator over
`S`, with the scalar-tower actions on its source and target form terms fixed canonically. -/
@[stacks 0G34]
def IsOrderOne (δ : Family R S M) (p : ℕ) : Prop :=
  -- Local instance justification (defeq pin): preserve the caller's degree-dependent scalar action.
  letI : Module R (exteriorPower.form S M p) :=
    exteriorPower.form.moduleOfScalarTower (A := R) (B := S) (M := M) p
  -- Local instance justification (defeq pin): preserve the caller's degree-dependent scalar action.
  letI : Module R (exteriorPower.form S M (p + 1)) :=
    exteriorPower.form.moduleOfScalarTower (A := R) (B := S) (M := M) (p + 1)
  -- Local instance justification (defeq pin): preserve the canonical scalar-tower witness for the fixed action.
  letI : SMulCommClass S R (exteriorPower.form S M p) :=
    exteriorPower.form.smulCommClass_moduleOfScalarTower (A := R) (B := S) (M := M) p
  -- Local instance justification (defeq pin): preserve the canonical scalar-tower witness for the fixed action.
  letI : SMulCommClass S R (exteriorPower.form S M (p + 1)) :=
    exteriorPower.form.smulCommClass_moduleOfScalarTower (A := R) (B := S) (M := M) (p + 1)
  (δ p).IsDifferentialOperatorOfOrder S 1

/-- If a derivation spans its target module, then every member of an
exterior-power family satisfying the de Rham formulas is a differential operator of order at most
one.  The square-zero relation is intentionally not required. -/
@[stacks 0G34]
theorem isOrderOne {D : Derivation R S M} {δ : Family R S M}
    (hδ : SatisfiesFormula D δ)
    (hspan : Submodule.span S (Set.range D) = ⊤)
    (p : ℕ) :
    IsOrderOne δ p := sorry

end

end DifferentialOperator.DeRham
