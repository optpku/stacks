/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import ReasLib.Algebra.Module.ClosedPointFiber
import Mathlib.Tactic.CrossRefAttribute

/-!
# Visible quotients of closed-point module fibers

This leaf owns the canonical quotient `V(x)` of a closed-point fiber by the vectors invisible to
global linear forms.  It also records the short exact sequence defining `V(x)` and the localized
splitting criterion for finitely presented modules.

@stack 0GV9
-/

@[expose] public section

open scoped ClosedPointFiber

universe u v

namespace Module.ClosedFiber

variable {R : Type u} [CommRing R]

/-- The composite `N → R → R / x` underlying the fiberwise linear form induced by
`φ : Module.Dual R N`. -/
@[stacks 0GV9 "quotient linear form over the base ring"]
noncomputable def quotientLinearFormBase
    (N : Type v) [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) (φ : Module.Dual R N) :
    N →ₗ[R] R ⧸ x.1.asIdeal :=
  (Ideal.Quotient.mkₐ R x.1.asIdeal).toLinearMap.comp φ

/-- The ideal multiple `xN` lies in the kernel of the quotient-valued form induced by `φ`. -/
theorem smulTop_le_ker_quotientLinearFormBase
    (N : Type v) [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) (φ : Module.Dual R N) :
    x.1.asIdeal • (⊤ : Submodule R N) ≤
      LinearMap.ker (quotientLinearFormBase N x φ) := sorry
-- Proof strategy: use `Submodule.smul_induction_on`; coefficients from `x` map to zero in
-- `R / x`, and the kernel is closed under addition.

/-- The `R`-linear map on `N(x)` induced by a global linear form, before transporting the target
from `R / x` to `κ(x)`. -/
@[stacks 0GV9 "quotient linear form on the closed-point fiber"]
noncomputable def quotientLinearFormMap
    (N : Type v) [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) (φ : Module.Dual R N) :
    N﹙x﹚ →ₗ[R] R ⧸ x.1.asIdeal :=
  (x.1.asIdeal • (⊤ : Submodule R N)).liftQ
    (quotientLinearFormBase N x φ)
    (smulTop_le_ker_quotientLinearFormBase N x φ)

/-- The quotient-valued fiber form respects the `R / x`-scalar action. -/
theorem quotientLinearFormMap_map_smul
    (N : Type v) [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) (φ : Module.Dual R N)
    (c : R ⧸ x.1.asIdeal) (q : N﹙x﹚) :
    quotientLinearFormMap N x φ (c • q) = c • quotientLinearFormMap N x φ q := sorry
-- Proof strategy: lift `c` through `Ideal.Quotient.mk_surjective` and `q` through the module
-- quotient map, then reduce both sides to linearity of `φ` and the quotient scalar formula.

/-- A global `R`-linear form induces an `(R / x)`-linear form on the quotient fiber. -/
@[stacks 0GV9 "quotient-valued closed-point fiber form"]
noncomputable def quotientLinearForm
    (N : Type v) [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) (φ : Module.Dual R N) :
    Module.Dual (R ⧸ x.1.asIdeal) (N﹙x﹚) :=
  { toFun := quotientLinearFormMap N x φ
    map_add' := (quotientLinearFormMap N x φ).map_add
    map_smul' := quotientLinearFormMap_map_smul N x φ }

/-- Additivity of the residue-field-valued form induced on the closed-point fiber. -/
theorem linearForm_map_add
    (N : Type v) [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) (φ : Module.Dual R N) (a b : N﹙x﹚) :
    residueFieldAlgEquiv (R := R) x (quotientLinearForm N x φ (a + b)) =
      residueFieldAlgEquiv (R := R) x (quotientLinearForm N x φ a) +
        residueFieldAlgEquiv (R := R) x (quotientLinearForm N x φ b) := sorry
-- Proof strategy: rewrite with `map_add` for `quotientLinearForm` and then with `map_add` for
-- `residueFieldAlgEquiv`.

/-- Compatibility of the induced fiber form with the `κ(x)`-scalar action. -/
theorem linearForm_map_smul
    (N : Type v) [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) (φ : Module.Dual R N)
    (c : κ(x)) (q : N﹙x﹚) :
    residueFieldAlgEquiv (R := R) x (quotientLinearForm N x φ (c • q)) =
      c • residueFieldAlgEquiv (R := R) x (quotientLinearForm N x φ q) := sorry
-- Proof strategy: express the `κ(x)` action through `residueFieldAlgEquiv.symm`, apply
-- `quotientLinearForm.map_smul`, and transport multiplication back through the algebra equivalence.

/-- The `κ(x)`-linear form on `N(x)` induced by a global `R`-linear form. -/
@[stacks 0GV9 "canonical closed-point fiber linear form"]
noncomputable def linearForm
    (N : Type v) [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) (φ : Module.Dual R N) :
    Module.Dual κ(x) (N﹙x﹚) :=
  { toFun := fun q ↦ residueFieldAlgEquiv (R := R) x (quotientLinearForm N x φ q)
    map_add' := linearForm_map_add N x φ
    map_smul' := linearForm_map_smul N x φ }

/-- The invisible subspace `B(x)` is the common kernel of all fiberwise forms induced by global
`R`-linear forms. -/
@[stacks 0GV9 "invisible closed-point fiber subspace"]
noncomputable abbrev invisible
    (N : Type v) [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) : Submodule κ(x) (N﹙x﹚) :=
  (Submodule.span κ(x) (Set.range (linearForm N x))).dualCoannihilator

scoped[ClosedPointFiber] notation:max "B(" x:max ")" =>
  Module.ClosedFiber.invisible _ x

/-- The visible fiber `V(x)` is the quotient of `N(x)` by its invisible subspace. -/
@[stacks 0GV9 "visible closed-point fiber quotient"]
noncomputable abbrev Visible
    (N : Type v) [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) : Type v :=
  N﹙x﹚ ⧸ invisible N x

scoped[ClosedPointFiber] notation:max "V(" x:max ")" =>
  Module.ClosedFiber.Visible _ x

/-- The inclusion of `B(x)` into the full fiber `N(x)`. -/
@[stacks 0GV9 "invisible subspace inclusion"]
noncomputable def inclusion
    (N : Type v) [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) :
    invisible N x →ₗ[κ(x)] N﹙x﹚ :=
  (invisible N x).subtype

/-- The quotient map from `N(x)` to its visible quotient `V(x)`. -/
@[stacks 0GV9 "visible fiber quotient map"]
noncomputable def quotientMap
    (N : Type v) [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) :
    N﹙x﹚ →ₗ[κ(x)] Visible N x :=
  (invisible N x).mkQ

/-- The defining inclusion and quotient maps of the visible fiber have zero composite. -/
theorem quotientMap_comp_inclusion
    (N : Type v) [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) :
    (quotientMap N x).comp (inclusion N x) = 0 := sorry
-- Proof strategy: ext an element of `invisible N x`; `Submodule.mkQ` sends every element of the
-- quotienting submodule to zero.

/-- The canonical short complex `B(x) ⟶ N(x) ⟶ V(x)`. -/
@[stacks 0GV9 "canonical visible-fiber short complex"]
noncomputable abbrev sequence
    (N : Type v) [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) :
    CategoryTheory.ShortComplex (ModuleCat.{v} κ(x)) :=
  CategoryTheory.ShortComplex.moduleCatMk (inclusion N x) (quotientMap N x)
    (quotientMap_comp_inclusion N x)

/-- Lemma 15.128.2 (1), tag 0GV9: the canonical sequence
`0 ⟶ B(x) ⟶ N(x) ⟶ V(x) ⟶ 0` is short exact. -/
@[stacks 0GV9 "canonical visible-fiber short exact sequence"]
theorem shortExact
    (N : Type v) [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) : (sequence N x).ShortExact := sorry
-- Proof strategy: use the module-category short-exact criterion: the subtype inclusion is
-- injective, `Submodule.mkQ` is surjective, and its kernel is exactly `invisible N x`.

/-- The class in `V(x)` represented by the image of a global section in `N(x)`. -/
@[stacks 0GV9 "visible class of a global section"]
noncomputable abbrev visibleClass
    {N : Type v} [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) (s : N) : Visible N x :=
  quotientMap N x (Module.ClosedFiber.mk x s)

/-- Every visible class at a closed point is represented by a global section. -/
theorem visibleClass_surjective
    (N : Type v) [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) :
    Function.Surjective (visibleClass x : N → Visible N x) := sorry
-- Proof strategy: compose surjectivity of the original fiber quotient map with surjectivity of
-- `(invisible N x).mkQ`.

/-- Every global form vanishes on the invisible subspace of the fiber. -/
theorem invisible_le_ker_linearForm
    (N : Type v) [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) (φ : Module.Dual R N) :
    invisible N x ≤ LinearMap.ker (linearForm N x φ) := sorry
-- Proof strategy: unfold `invisible` as the dual coannihilator of the span of induced forms;
-- `linearForm N x φ` belongs to that span by `Submodule.subset_span`, so every invisible vector
-- evaluates to zero.

/-- The linear form on `V(x)` induced by a global `R`-linear form. -/
@[stacks 0GV9 "visible quotient linear form"]
noncomputable def visibleLinearForm
    (N : Type v) [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) (φ : Module.Dual R N) :
    Module.Dual κ(x) (Visible N x) :=
  (invisible N x).liftQ (linearForm N x φ) (invisible_le_ker_linearForm N x φ)

/-- Evaluation of an induced visible-fiber form on the class of a global section. -/
theorem visibleLinearForm_apply_visibleClass
    (N : Type v) [AddCommGroup N] [Module R N]
    (x : closedPoints (PrimeSpectrum R)) (φ : Module.Dual R N) (s : N) :
    visibleLinearForm N x φ (visibleClass x s) = algebraMap R κ(x) (φ s) := sorry
-- Proof strategy: unfold the two quotient lifts and evaluate on `Submodule.Quotient.mk s`; the
-- resulting residue-field value is the algebra-map image of `φ s`.

/-- For a finitely presented module, every linear form on `V(x)` is induced by a global
`R`-linear form. -/
@[stacks 0GV9 "surjectivity of global forms onto the visible dual"]
theorem visibleLinearForm_surjective
    (N : Type v) [AddCommGroup N] [Module R N] [Module.FinitePresentation R N]
    (x : closedPoints (PrimeSpectrum R)) :
    Function.Surjective (visibleLinearForm N x) := sorry
-- Proof strategy: finite presentation makes the fiber finite-dimensional. Identify the dual of
-- the quotient by a dual coannihilator with the span of the inducing fiber forms, then lift each
-- spanning form through the finite-presentation localization/base-change comparison for
-- `Module.Dual R N`.

/-- The `R`-linear map sending the standard basis of `R^r` to a selected family of sections. -/
@[stacks 0GV9 "linear map of selected sections"]
noncomputable abbrev selectedSectionsMap
    {N : Type v} [AddCommGroup N] [Module R N]
    {r : ℕ} (s : Fin r → N) : (Fin r → R) →ₗ[R] N :=
  (Pi.basisFun R (Fin r)).constr R s

/-- The selected sections split after inverting an element away from `x` when their localized map
admits a left inverse. -/
@[stacks 0GV9 "selected sections split after localization"]
def SelectedSectionsSplitAfterInverting
    {N : Type v} [AddCommGroup N] [Module R N]
    {r : ℕ} (x : closedPoints (PrimeSpectrum R)) (s : Fin r → N) : Prop :=
  ∃ f : R, f ∉ x.1.asIdeal ∧
    ∃ ρ : LocalizedModule.Away f N →ₗ[Localization.Away f]
        LocalizedModule.Away f (Fin r → R),
      Function.LeftInverse ρ
        (LocalizedModule.map (Submonoid.powers f) (selectedSectionsMap s))

/-- Lemma 15.128.2 (2), tag 0GV9: selected sections split off a free summand after localization
away from `x` exactly when their classes in `V(x)` are linearly independent. -/
@[stacks 0GV9 "localized splitting and visible-class independence"]
theorem selectedSectionsSplitAfterInverting_iff_linearIndependent
    {N : Type v} [AddCommGroup N] [Module R N] [Module.FinitePresentation R N]
    (x : closedPoints (PrimeSpectrum R)) {r : ℕ} (s : Fin r → N) :
    SelectedSectionsSplitAfterInverting x s ↔
      LinearIndependent κ(x) (visibleClass x ∘ s) := sorry
-- Proof strategy: a localized left inverse yields coordinate forms whose reductions separate the
-- visible classes. Conversely extend the independent visible classes to coordinate forms, lift
-- them globally using `visibleLinearForm_surjective`, and invert one element outside `x` so the
-- resulting matrix identities give a left inverse to the localized selected-sections map.

end Module.ClosedFiber
