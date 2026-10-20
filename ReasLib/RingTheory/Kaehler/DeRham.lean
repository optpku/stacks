/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.DifferentialOperator.DeRham
public import ReasLib.LinearAlgebra.Quotient.Descent
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The algebraic de Rham complex

@stack 0FKF
@stack 0FKG

This file owns an explicit presentation of algebraic differential forms.  The degree `p` form
module is the free `B`-module on symbols `b₀ db₁ ∧ ... ∧ dbₚ`, modulo exactly the relations seen in
the standard exterior power.  Restriction of scalars produces the `A`-module underlying the de Rham
complex, whose differential is induced directly on generators.
-/

@[expose] public section

noncomputable section

open CategoryTheory ComplexShape

universe u

namespace KaehlerDifferential.DeRham

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- An index for a basic `p`-form `b₀ db₁ ∧ ... ∧ dbₚ`. -/
abbrev Generator (B : Type u) (p : ℕ) := B × (Fin p → B)

/-- The free `B`-module on basic `p`-forms. -/
abbrev Free (B : Type u) [CommRing B] (p : ℕ) := Generator B p →₀ B

/-- The free `B`-module on basic `p`-forms, bundled as a module object. -/
abbrev free (p : ℕ) : ModuleCat.{u} B := ModuleCat.of B (Free B p)

/-- The standard exterior-power module of relative differential `p`-forms. -/
@[stacks 0FKF]
def exteriorForm (p : ℕ) : ModuleCat.{u} B :=
  ModuleCat.of B (exteriorPower.form B Ω[B⁄A] p)

/-- Evaluation of formal basic forms in the standard exterior-power module. -/
@[stacks 0FKF]
def evaluation (p : ℕ) : free B p ⟶ exteriorForm A B p :=
  ModuleCat.ofHom <| Finsupp.linearCombination B fun x ↦
    DifferentialOperator.DeRham.basicForm (KaehlerDifferential.D A B) p x.1 x.2

/-- Relations between formal basic forms are the kernel of evaluation in the standard exterior
power. -/
abbrev relations (p : ℕ) : Submodule B (free B p) :=
  LinearMap.ker (evaluation A B p).hom

/-- The explicit basic-form presentation of relative differential `p`-forms. -/
@[stacks 0FKF]
abbrev Form (p : ℕ) := Free B p ⧸ relations A B p

/-- Relative differential `p`-forms, retaining their natural `B`-module structure. -/
@[stacks 0FKF]
abbrev form (p : ℕ) : ModuleCat.{u} B := ModuleCat.of B (Form A B p)

/-- The `A`-module underlying relative differential `p`-forms. -/
@[stacks 0FKF]
abbrev term (p : ℕ) : ModuleCat.{u} A :=
  (ModuleCat.restrictScalars (algebraMap A B)).obj (form A B p)

/-- The quotient map from formal basic forms to relative differential forms. -/
def quotient (p : ℕ) : free B p ⟶ form A B p :=
  ModuleCat.ofHom (relations A B p).mkQ

/-- The quotient map commutes with the scalar action induced from a coefficient ring. -/
theorem quotientRestrictScalars_smul (R : Type u) [CommRing R] [Algebra R B]
    (p : ℕ) (r : R) (x : Free B p) :
    (relations A B p).mkQ (r • x) =
      @SMul.smul R (RestrictScalars R B (Form A B p)) inferInstance r
        ((relations A B p).mkQ x) := sorry

/-- The quotient map on formal differential forms, viewed over a coefficient ring. -/
def quotientRestrictScalars (R : Type u) [CommRing R] [Algebra R B] (p : ℕ) :
    Free B p →ₗ[R] RestrictScalars R B (Form A B p) where
  toFun := (relations A B p).mkQ
  map_add' := (relations A B p).mkQ.map_add
  map_smul' := quotientRestrictScalars_smul A B R p

/-- Restricting scalars does not change the quotient class of a formal form. -/
theorem quotientRestrictScalars_apply (R : Type u) [CommRing R] [Algebra R B]
    (p : ℕ) (x : Free B p) :
    quotientRestrictScalars A B R p x = Submodule.Quotient.mk x := rfl

/-- Every relative differential form has a formal representative. -/
theorem quotientRestrictScalars_surjective (R : Type u) [CommRing R] [Algebra R B]
    (p : ℕ) : Function.Surjective (quotientRestrictScalars A B R p) :=
  (relations A B p).mkQ_surjective

/-- The kernel of the scalar-restricted quotient map is the module of relations. -/
theorem quotientRestrictScalars_ker (R : Type u) [CommRing R] [Algebra R B]
    (p : ℕ) : LinearMap.ker (quotientRestrictScalars A B R p) =
      (relations A B p).restrictScalars R := sorry

/-- Evaluate a rule on a chosen representative of a relative form. -/
noncomputable def descendRestrictScalarsFun (R : Type u) [CommRing R] [Algebra R B]
    {M : Type u} [AddCommGroup M] [Module R M] (p : ℕ)
    (f : Free B p →ₗ[R] M) : RestrictScalars R B (Form A B p) → M :=
  fun x ↦ f (Function.surjInv (quotientRestrictScalars_surjective A B R p) x)

/-- A rule vanishing on relations is additive on chosen quotient representatives. -/
theorem descendRestrictScalarsFun_add (R : Type u) [CommRing R] [Algebra R B]
    {M : Type u} [AddCommGroup M] [Module R M] (p : ℕ) (f : Free B p →ₗ[R] M)
    (h : (relations A B p).restrictScalars R ≤ LinearMap.ker f)
    (x y : RestrictScalars R B (Form A B p)) :
    descendRestrictScalarsFun A B R p f (x + y) =
      descendRestrictScalarsFun A B R p f x + descendRestrictScalarsFun A B R p f y := sorry

/-- A rule vanishing on relations respects the coefficient action on quotient representatives. -/
theorem descendRestrictScalarsFun_smul (R : Type u) [CommRing R] [Algebra R B]
    {M : Type u} [AddCommGroup M] [Module R M] (p : ℕ) (f : Free B p →ₗ[R] M)
    (h : (relations A B p).restrictScalars R ≤ LinearMap.ker f)
    (r : R) (x : RestrictScalars R B (Form A B p)) :
    descendRestrictScalarsFun A B R p f (r • x) =
      r • descendRestrictScalarsFun A B R p f x := sorry

/-- Descend a coefficient-linear rule that vanishes on the relations between basic forms.
Its value is independent of the representative because the rule kills those relations. -/
noncomputable def descendRestrictScalars (R : Type u) [CommRing R] [Algebra R B]
    {M : Type u} [AddCommGroup M] [Module R M] (p : ℕ) (f : Free B p →ₗ[R] M)
    (h : (relations A B p).restrictScalars R ≤ LinearMap.ker f) :
    RestrictScalars R B (Form A B p) →ₗ[R] M where
  toFun := descendRestrictScalarsFun A B R p f
  map_add' := descendRestrictScalarsFun_add A B R p f h
  map_smul' := descendRestrictScalarsFun_smul A B R p f h

/-- The descended rule agrees with the rule on a formal representative. -/
theorem descendRestrictScalars_quotient (R : Type u) [CommRing R] [Algebra R B]
    {M : Type u} [AddCommGroup M] [Module R M] (p : ℕ)
    (f : Free B p →ₗ[R] M)
    (h : (relations A B p).restrictScalars R ≤ LinearMap.ker f) (x : Free B p) :
    descendRestrictScalars A B R p f h (quotientRestrictScalars A B R p x) = f x := sorry

/-- The class of the basic form `b₀ db₁ ∧ ... ∧ dbₚ`. -/
def basic (p : ℕ) (b₀ : B) (b : Fin p → B) : form A B p :=
  quotient A B p (Finsupp.single (b₀, b) 1)

/-- The class of the exact form `db₁ ∧ ... ∧ dbₚ`. -/
def exact (p : ℕ) (b : Fin p → B) : form A B p :=
  basic A B p 1 b

/-- The evaluation relations viewed after restricting scalars from `B` to `A`. -/
abbrev aRelations (p : ℕ) : Submodule A (free B p) :=
  (relations A B p).restrictScalars A

/-- The scalar-restricted quotient presentation used to define the differential explicitly. -/
abbrev AForm (p : ℕ) := Free B p ⧸ aRelations A B p

/-- The scalar-restricted quotient presentation as an `A`-module object. -/
abbrev aForm (p : ℕ) : ModuleCat.{u} A := ModuleCat.of A (AForm A B p)

/-- The free basic-form module viewed over `A` through the given algebra structure. -/
abbrev aFree (p : ℕ) : ModuleCat.{u} A := ModuleCat.of A (Free B p)

/-- The quotient comparison respects scalar multiplication in the bundled restriction-of-scalars
module. -/
theorem termLinearEquiv_smul (p : ℕ) (r : A) (x : AForm A B p) :
    (Submodule.Quotient.restrictScalarsEquiv A (relations A B p)) (r • x) =
      ((term A B p).smul r).hom
        ((Submodule.Quotient.restrictScalarsEquiv A (relations A B p)) x) := sorry

/-- The explicit scalar-restricted quotient is linearly equivalent to restriction of scalars on
forms; its underlying equivalence is the identity on quotient classes. -/
def termLinearEquiv (p : ℕ) : AForm A B p ≃ₗ[A] term A B p where
  toFun := Submodule.Quotient.restrictScalarsEquiv A (relations A B p)
  invFun := (Submodule.Quotient.restrictScalarsEquiv A (relations A B p)).symm
  left_inv := (Submodule.Quotient.restrictScalarsEquiv A (relations A B p)).left_inv
  right_inv := (Submodule.Quotient.restrictScalarsEquiv A (relations A B p)).right_inv
  map_add' := (Submodule.Quotient.restrictScalarsEquiv A (relations A B p)).map_add
  map_smul' := termLinearEquiv_smul A B p

/-- The explicit scalar-restricted quotient agrees with restriction of scalars on forms. -/
def termIso (p : ℕ) : aForm A B p ≅ term A B p :=
  (termLinearEquiv A B p).toModuleIso

/-- A basic form in the explicit scalar-restricted quotient presentation. -/
def aBasic (p : ℕ) (b₀ : B) (b : Fin p → B) : aForm A B p :=
  (aRelations A B p).mkQ (Finsupp.single (b₀, b) 1)

/-- An exact form in the explicit scalar-restricted quotient presentation. -/
def aExact (p : ℕ) (b : Fin p → B) : aForm A B p :=
  aBasic A B p 1 b

/-- Multiplying the coefficient of a fixed formal basic form is additive after applying the de Rham
rule. -/
theorem coefficientTarget_add (p : ℕ) (x : Generator B p) (c c' : B) :
    aExact A B (p + 1) (Fin.cons ((c + c') * x.1) x.2) =
      aExact A B (p + 1) (Fin.cons (c * x.1) x.2) +
        aExact A B (p + 1) (Fin.cons (c' * x.1) x.2) := sorry

/-- Multiplying the coefficient of a fixed formal basic form is `A`-linear after applying the de
Rham rule. -/
theorem coefficientTarget_smul (p : ℕ) (x : Generator B p) (r : A) (c : B) :
    aExact A B (p + 1) (Fin.cons ((r • c) * x.1) x.2) =
      r • aExact A B (p + 1) (Fin.cons (c * x.1) x.2) := sorry

/-- The `A`-linear contribution of the coefficient of one formal basic form to its differential. -/
def coefficientTarget (p : ℕ) (x : Generator B p) : B →ₗ[A] aForm A B (p + 1) where
  toFun c := aExact A B (p + 1) (Fin.cons (c * x.1) x.2)
  map_add' := coefficientTarget_add A B p x
  map_smul' := coefficientTarget_smul A B p x

/-- The de Rham rule on the free basic-form presentation, as an `A`-linear map. -/
def target (p : ℕ) :
    aFree A B p ⟶ aForm A B (p + 1) :=
  ModuleCat.ofHom <| Finsupp.lsum A (coefficientTarget A B p)

/-- The basic-form de Rham rule respects the scalar-restricted evaluation relations. -/
theorem aRelations_le_ker_target (p : ℕ) :
    aRelations A B p ≤ LinearMap.ker (target A B p).hom := sorry

/-- The differential on the explicit scalar-restricted quotient presentation. -/
def rawD (p : ℕ) : aForm A B p ⟶ aForm A B (p + 1) :=
  ModuleCat.ofHom <|
    (aRelations A B p).liftQ (target A B p).hom (aRelations_le_ker_target A B p)

/-- The canonical `A`-linear differential on relative differential forms. -/
@[stacks 0FKF]
def d (p : ℕ) : term A B p ⟶ term A B (p + 1) :=
  (termIso A B p).inv ≫ rawD A B p ≫ (termIso A B (p + 1)).hom

/-- The differential sends
`b₀ db₁ ∧ ... ∧ dbₚ` to `db₀ ∧ db₁ ∧ ... ∧ dbₚ`. -/
@[stacks 0FKG]
theorem d_basic (p : ℕ) (b₀ : B) (b : Fin p → B) :
    d A B p (basic A B p b₀ b) = exact A B (p + 1) (Fin.cons b₀ b) := sorry

/-- Consecutive differentials in the algebraic de Rham complex compose to zero. -/
theorem d_sq (p : ℕ) :
    d A B p ≫ d A B (p + 1) = 0 := sorry

/-- The algebraic de Rham complex of `B` over `A`. -/
@[stacks 0FKF]
def complex : CochainComplex (ModuleCat.{u} A) ℕ :=
  CochainComplex.of (term A B) (d A B) (d_sq A B)

/-- The degree-`p` object of the de Rham complex is the scalar-restricted form module. -/
theorem complex_X (p : ℕ) :
    (complex A B).X p = term A B p := sorry

/-- The consecutive-degree differential of the de Rham complex is `d A B p`. -/
theorem complex_d (p : ℕ) :
    (complex A B).d p (p + 1) = d A B p := sorry

/-- The presented form maps canonically to the standard exterior-power form by evaluation. -/
@[stacks 0FKF]
def toExterior (p : ℕ) : form A B p ⟶ exteriorForm A B p :=
  ModuleCat.ofHom <|
    (relations A B p).liftQ (evaluation A B p).hom le_rfl

/-- Evaluation carries a presented basic form to the corresponding standard exterior form. -/
theorem toExterior_basic (p : ℕ) (b₀ : B) (b : Fin p → B) :
    toExterior A B p (basic A B p b₀ b) =
      DifferentialOperator.DeRham.basicForm (KaehlerDifferential.D A B) p b₀ b := sorry

/-- Evaluation identifies the presented form module with the standard exterior-power module. -/
theorem toExterior_bijective (p : ℕ) :
    Function.Bijective (toExterior A B p) := sorry

end KaehlerDifferential.DeRham
