/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.DifferentialOperator.DeRham
public import ReasLib.LinearAlgebra.Quotient.Descent
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Data.Fintype.Quotient
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
      DifferentialOperator.DeRham.basicForm (KaehlerDifferential.D A B) p b₀ b := by
  change Finsupp.linearCombination B
    (fun x : Generator B p ↦
      DifferentialOperator.DeRham.basicForm (KaehlerDifferential.D A B) p x.1 x.2)
    (Finsupp.single (b₀, b) 1) = _
  simp

/-- Quotienting by evaluation's kernel already makes the forward comparison injective. -/
theorem toExterior_injective (p : ℕ) :
    Function.Injective (toExterior A B p) := by
  exact LinearMap.ker_eq_bot.mp
    ((relations A B p).ker_liftQ_eq_bot (evaluation A B p).hom le_rfl le_rfl)


namespace ExteriorComparison

/-- Extend a rule on tuples of differential symbols by finite sums in each slot.
This recursion uses the actual coefficients of each finitely supported input. -/
def expand {N : Type u} [AddCommGroup N] [Module B N] :
    (p : ℕ) → ((Fin p → B) → N) → (Fin p → (B →₀ B)) → N
  | 0, f, _ => f Fin.elim0
  | p + 1, f, m => (m 0).sum fun b c ↦
      c • expand p (fun bs ↦ f (Fin.cons b bs)) (Fin.tail m)

/-- On unit differential symbols the finite-sum extension is the original rule. -/
theorem expand_single_one {N : Type u} [AddCommGroup N] [Module B N]
    (p : ℕ) (f : (Fin p → B) → N) (b : Fin p → B) :
    expand B p f (fun i ↦ Finsupp.single (b i) 1) = f b := by
  induction p with
  | zero =>
      exact congrArg f (Subsingleton.elim _ _)
  | succ p ih =>
      simp only [expand, Finsupp.sum_single_index, zero_smul, one_smul]
      change expand B p (fun bs ↦ f (Fin.cons (b 0) bs))
        (fun i ↦ Finsupp.single (b i.succ) 1) = f b
      rw [ih]
      exact congrArg f (Fin.cons_self_tail b)

/-- The explicit multilinear expansion of an exact form on free differential symbols. -/
def freeWedge (p : ℕ) (m : Fin p → (B →₀ B)) : Form A B p :=
  expand B p (exact A B p) m

/-- Kähler relations in any input slot do not change the resulting quotient class. -/
theorem freeWedge_respects (p : ℕ) (x y : Fin p → (B →₀ B))
    (h : ∀ i, (KaehlerDifferential.kerTotal A B).mkQ (x i) =
      (KaehlerDifferential.kerTotal A B).mkQ (y i)) :
    freeWedge A B p x = freeWedge A B p y := by
  sorry

/-- Descend the actual expansion through the finite family of Kähler quotients.
`Quotient.finLiftOn` is a finite quotient eliminator and does not select representatives. -/
def quotientWedge (p : ℕ)
    (m : Fin p → ((B →₀ B) ⧸ KaehlerDifferential.kerTotal A B)) : Form A B p :=
  Quotient.finLiftOn m (freeWedge A B p)
    (fun x y h ↦ freeWedge_respects A B p x y (fun i ↦ Quotient.sound (h i)))

/-- The canonical map to the symbol presentation is the lift of its universal derivation. -/
def differentialPresentation : Ω[B⁄A] →ₗ[B]
    ((B →₀ B) ⧸ KaehlerDifferential.kerTotal A B) :=
  (KaehlerDifferential.derivationQuotKerTotal A B).liftKaehlerDifferential

/-- Alternating multiplication of arbitrary Kähler differentials into presented forms.
Its function is a quotient lift of a finite sum of the specified basic generators. -/
def wedge (p : ℕ) : Ω[B⁄A] [⋀^Fin p]→ₗ[B] Form A B p where
  toFun m := quotientWedge A B p (fun i ↦ differentialPresentation A B (m i))
  map_update_add' := by
    sorry
  map_update_smul' := by
    sorry
  map_eq_zero_of_eq' := by
    sorry

/-- The alternating lift computes on actual universal differential generators. -/
theorem wedge_d (p : ℕ) (b : Fin p → B) :
    wedge A B p (fun i ↦ KaehlerDifferential.D A B (b i)) = exact A B p b := by
  change quotientWedge A B p
    (fun i ↦ differentialPresentation A B (KaehlerDifferential.D A B (b i))) = _
  simp only [differentialPresentation, Derivation.liftKaehlerDifferential_comp_D,
    KaehlerDifferential.derivationQuotKerTotal_apply]
  change Quotient.finLiftOn
    (fun i ↦ Quotient.mk (Submodule.quotientRel (KaehlerDifferential.kerTotal A B))
      (Finsupp.single (b i) 1)) (freeWedge A B p) _ = _
  rw [Quotient.finLiftOn_mk]
  exact expand_single_one B p (exact A B p) b

/-- The reverse comparison in degree zero sends a scalar to its basic-form class. -/
def zero : B →ₗ[B] Form A B 0 where
  toFun b := basic A B 0 b Fin.elim0
  map_add' := by
    sorry
  map_smul' := by
    sorry

/-- The reverse comparison in degree one uses the same explicit alternating lift. -/
def one : Ω[B⁄A] →ₗ[B] Form A B 1 where
  toFun m := wedge A B 1 (fun _ ↦ m)
  map_add' := by
    sorry
  map_smul' := by
    sorry

end ExteriorComparison

/-- The explicit inverse of evaluation: scalars in degree zero, the universal Kähler
quotient lift in degree one, and the universal alternating map in every higher degree. -/
@[stacks 0FKF]
def fromExterior : (p : ℕ) → exteriorForm A B p ⟶ form A B p
  | 0 => ModuleCat.ofHom (ExteriorComparison.zero A B)
  | 1 => ModuleCat.ofHom (ExteriorComparison.one A B)
  | p + 2 => ModuleCat.ofHom <|
      exteriorPower.alternatingMapLinearEquiv (ExteriorComparison.wedge A B (p + 2))

/-- The scalar component of the inverse is its specified quotient generator. -/
theorem fromExterior_zero_apply (b : B) :
    fromExterior A B 0 b = basic A B 0 b Fin.elim0 := rfl

/-- The degree-one component retains the actual quotient-lift function. -/
theorem fromExterior_one_apply (m : Ω[B⁄A]) :
    fromExterior A B 1 m = ExteriorComparison.quotientWedge A B 1
      (fun _ ↦ ExteriorComparison.differentialPresentation A B m) := rfl

/-- Exact exterior generators map to their presented quotient classes. -/
theorem fromExterior_exact (p : ℕ) (b : Fin p → B) :
    fromExterior A B p
      (DifferentialOperator.DeRham.exactForm (KaehlerDifferential.D A B) p b) =
      exact A B p b := by
  rcases p with _ | _ | p
  · change basic A B 0 1 Fin.elim0 = basic A B 0 1 b
    exact congrArg (basic A B 0 1) (Subsingleton.elim _ _)
  · change ExteriorComparison.wedge A B 1
        (fun _ ↦ KaehlerDifferential.D A B (b 0)) = exact A B 1 b
    have hb : (fun _ : Fin 1 ↦ b 0) = b := by
      funext i
      exact congrArg b (Fin.eq_zero i).symm
    simpa only [hb] using ExteriorComparison.wedge_d A B 1 (fun _ ↦ b 0)
  · exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti
      (ExteriorComparison.wedge A B (p + 2))
      (fun i ↦ KaehlerDifferential.D A B (b i)) |>.trans
        (ExteriorComparison.wedge_d A B (p + 2) b)

/-- A coefficient in a basic generator is its natural module scalar. -/
theorem basic_eq_smul_exact (p : ℕ) (b₀ : B) (b : Fin p → B) :
    basic A B p b₀ b = b₀ • exact A B p b := by
  apply toExterior_injective A B p
  let f : Form A B p →ₗ[B] exteriorPower.form B Ω[B⁄A] p := (toExterior A B p).hom
  change f (basic A B p b₀ b) = f (b₀ • exact A B p b)
  rw [f.map_smul]
  change toExterior A B p (basic A B p b₀ b) =
    b₀ • toExterior A B p (basic A B p 1 b)
  rw [toExterior_basic, toExterior_basic]
  simp only [DifferentialOperator.DeRham.basicForm, one_smul]
  rfl

/-- The inverse computes on every basic exterior generator, in all characteristics. -/
theorem fromExterior_basic (p : ℕ) (b₀ : B) (b : Fin p → B) :
    fromExterior A B p
      (DifferentialOperator.DeRham.basicForm (KaehlerDifferential.D A B) p b₀ b) =
      basic A B p b₀ b := by
  let f : exteriorPower.form B Ω[B⁄A] p →ₗ[B] Form A B p :=
    (fromExterior A B p).hom
  change f (b₀ • DifferentialOperator.DeRham.exactForm (KaehlerDifferential.D A B) p b) = _
  rw [f.map_smul]
  change b₀ • fromExterior A B p
    (DifferentialOperator.DeRham.exactForm (KaehlerDifferential.D A B) p b) = _
  rw [fromExterior_exact, basic_eq_smul_exact]

/-- Both directions are fixed independently before the inverse laws are stated. -/
theorem toExterior_fromExterior (p : ℕ) (x : exteriorForm A B p) :
    toExterior A B p (fromExterior A B p x) = x := by
  sorry

/-- The other inverse law is an equality of actual quotient-lift maps. -/
theorem fromExterior_toExterior (p : ℕ) (x : form A B p) :
    fromExterior A B p (toExterior A B p x) = x := by
  let f : Form A B p →ₗ[B] Form A B p :=
    (fromExterior A B p).hom.comp (toExterior A B p).hom
  have hgen (t : Generator B p) :
      f (basic A B p t.1 t.2) = basic A B p t.1 t.2 := by
    change fromExterior A B p (toExterior A B p (basic A B p t.1 t.2)) = _
    rw [toExterior_basic, fromExterior_basic]
  have hf : f.comp (relations A B p).mkQ = (relations A B p).mkQ := by
    apply Finsupp.lhom_ext
    intro t c
    have hc : Finsupp.single t c = c • Finsupp.single t 1 := by
      simp
    simp only [LinearMap.comp_apply, hc, map_smul]
    change c • f (basic A B p t.1 t.2) = c • basic A B p t.1 t.2
    rw [hgen]
  obtain ⟨z, rfl⟩ := (relations A B p).mkQ_surjective x
  exact LinearMap.congr_fun hf z

/-- Evaluation identifies the presented form module with standard exterior forms by the
specified inverse, rather than using bijectivity to choose inverse data. -/
theorem toExterior_bijective (p : ℕ) :
    Function.Bijective (toExterior A B p) :=
  ⟨toExterior_injective A B p,
    fun x ↦ ⟨fromExterior A B p x, toExterior_fromExterior A B p x⟩⟩

/-- The explicit comparison as a linear equivalence, without choosing inverse data. -/
def exteriorLinearEquiv (p : ℕ) : Form A B p ≃ₗ[B] exteriorForm A B p where
  toFun := toExterior A B p
  invFun := fromExterior A B p
  left_inv := fromExterior_toExterior A B p
  right_inv := toExterior_fromExterior A B p
  map_add' := (toExterior A B p).hom.map_add
  map_smul' := (toExterior A B p).hom.map_smul

/-- The canonical isomorphism between presented and standard exterior forms. -/
def exteriorIso (p : ℕ) : form A B p ≅ exteriorForm A B p :=
  (exteriorLinearEquiv A B p).toModuleIso


/-- Mathlib's canonical degree-zero and degree-one identifications relate the uniform exterior
power to the degreewise exterior-form convention; higher degrees use the identity. -/
def standardExteriorEquiv : (p : ℕ) →
    (⋀[B]^p Ω[B⁄A]) ≃ₗ[B] exteriorForm A B p
  | 0 => exteriorPower.zeroEquiv B Ω[B⁄A]
  | 1 => exteriorPower.oneEquiv B Ω[B⁄A]
  | p + 2 => LinearEquiv.refl B _

/-- Presented forms compare with the uniform exterior power used by geometric stalks. -/
def exteriorPowerEquiv (p : ℕ) : Form A B p ≃ₗ[B] (⋀[B]^p Ω[B⁄A]) :=
  (exteriorLinearEquiv A B p).trans (standardExteriorEquiv A B p).symm

namespace SquareNaturality

variable {A A' B B' : Type u}
variable [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
variable [Algebra A B] [Algebra A' B']

/-- Apply the total-ring map to a free differential symbol and its coefficient. -/
def differentialSymbols (b : B →+* B') : (B →₀ B) →ₛₗ[b] (B' →₀ B') :=
  (Finsupp.lmapDomain B' B' b).comp (Finsupp.mapRange.linearMap b.toSemilinearMap)

/-- A commuting ring square preserves the actual Kähler relations on symbols. -/
theorem differentialSymbols_relations (a : A →+* A') (b : B →+* B')
    (h : (algebraMap A' B').comp a = b.comp (algebraMap A B)) :
    KaehlerDifferential.kerTotal A B ≤
      (KaehlerDifferential.kerTotal A' B').comap (differentialSymbols b) := by
  sorry

/-- The semilinear Kähler map for an arbitrary commuting ring square is obtained by mapping
symbols through the explicit presentation quotients. -/
def differentialMap (a : A →+* A') (b : B →+* B')
    (h : (algebraMap A' B').comp a = b.comp (algebraMap A B)) :
    Ω[B⁄A] →ₛₗ[b] Ω[B'⁄A'] :=
  (KaehlerDifferential.quotKerTotalEquiv A' B').toLinearMap.comp
    (((KaehlerDifferential.kerTotal A B).mapQ
      (KaehlerDifferential.kerTotal A' B') (differentialSymbols b)
      (differentialSymbols_relations a b h)).comp
        (ExteriorComparison.differentialPresentation A B))

/-- The alternating product of the images of the actual Kähler map, with scalar restriction
specified directly by the given total-ring homomorphism. -/
def exteriorWedge (a : A →+* A') (b : B →+* B')
    (h : (algebraMap A' B').comp a = b.comp (algebraMap A B)) (p : ℕ) :
    letI : Module B (⋀[B']^p Ω[B'⁄A']) := Module.compHom _ b
    Ω[B⁄A] [⋀^Fin p]→ₗ[B] (⋀[B']^p Ω[B'⁄A']) :=
  letI : Module B (⋀[B']^p Ω[B'⁄A']) := Module.compHom _ b
  { toFun m := exteriorPower.ιMulti B' p (fun i ↦ differentialMap a b h (m i))
    map_update_add' := by sorry
    map_update_smul' := by sorry
    map_eq_zero_of_eq' := by sorry }

/-- The standard exterior-form map induced by an arbitrary commuting ring square. -/
def exteriorMap (a : A →+* A') (b : B →+* B')
    (h : (algebraMap A' B').comp a = b.comp (algebraMap A B)) :
    (p : ℕ) → exteriorPower.form B Ω[B⁄A] p →ₛₗ[b]
      exteriorPower.form B' Ω[B'⁄A'] p
  | 0 => b.toSemilinearMap
  | 1 => differentialMap a b h
  | p + 2 => by
      letI : Module B (⋀[B']^(p + 2) Ω[B'⁄A']) := Module.compHom _ b
      let f : (⋀[B]^(p + 2) Ω[B⁄A]) →ₗ[B] (⋀[B']^(p + 2) Ω[B'⁄A']) :=
        exteriorPower.alternatingMapLinearEquiv (exteriorWedge a b h (p + 2))
      exact
        { toFun := f
          map_add' := f.map_add
          map_smul' := by sorry }

/-- Apply a total-ring map to every entry of a basic-form index. -/
def basicIndex (b : B →+* B') (p : ℕ) : Generator B p → Generator B' p :=
  fun x ↦ (b x.1, fun i ↦ b (x.2 i))

/-- The free basic-form map uses the same specified coefficient homomorphism. -/
def basicSymbols (b : B →+* B') (p : ℕ) : Free B p →ₛₗ[b] Free B' p :=
  (Finsupp.lmapDomain B' B' (basicIndex b p)).comp
    (Finsupp.mapRange.linearMap b.toSemilinearMap)

/-- A commuting ring square preserves evaluation relations on basic forms. -/
theorem basicSymbols_relations (a : A →+* A') (b : B →+* B')
    (h : (algebraMap A' B').comp a = b.comp (algebraMap A B)) (p : ℕ) :
    relations A B p ≤ (relations A' B' p).comap (basicSymbols b p) := by
  sorry

/-- The actual quotient map on forms for a commuting ring square. -/
def presentedMap (a : A →+* A') (b : B →+* B')
    (h : (algebraMap A' B').comp a = b.comp (algebraMap A B)) (p : ℕ) :
    Form A B p →ₛₗ[b] Form A' B' p :=
  (relations A B p).mapQ (relations A' B' p) (basicSymbols b p)
    (basicSymbols_relations a b h p)

/-- The reverse comparison is natural for arbitrary commuting squares of commutative rings. -/
theorem fromExterior_naturality (a : A →+* A') (b : B →+* B')
    (h : (algebraMap A' B').comp a = b.comp (algebraMap A B))
    (p : ℕ) (x : exteriorForm A B p) :
    presentedMap a b h p (fromExterior A B p x) =
      fromExterior A' B' p (exteriorMap a b h p x) := by
  sorry

/-- Forward evaluation is natural for the same independently defined square maps. -/
theorem toExterior_naturality (a : A →+* A') (b : B →+* B')
    (h : (algebraMap A' B').comp a = b.comp (algebraMap A B))
    (p : ℕ) (x : Form A B p) :
    toExterior A' B' p (presentedMap a b h p x) =
      exteriorMap a b h p (toExterior A B p x) := by
  sorry

end SquareNaturality

end KaehlerDifferential.DeRham
