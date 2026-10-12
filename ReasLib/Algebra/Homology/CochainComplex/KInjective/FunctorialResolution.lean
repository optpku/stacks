/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.CochainComplex.FunctorialApproximation
public import ReasLib.Algebra.Homology.CochainComplex.KInjective.Resolution

@[expose] public section

/-!
# Functorial K-Injective Resolutions

This module refines the neutral `FunctorialComplexApproximation` owner by recording the two
properties needed to compute unbounded right-derived functors: injectivity in every degree and
K-injectivity of every target complex. The construction of such a refinement is kept separate
from its reusable data and projection API.
-/

open CategoryTheory

universe w v u

namespace CochainComplex

variable (C : Type u) [Category.{v} C] [Abelian C]

namespace KInjectiveResolution

/-- A functorial K-injective resolution is a functorial complex approximation whose target has
injective terms and is K-injective for every input complex. -/
@[stacks 079P "functorial K-injective resolution"]
structure Functorial extends
    toApproximation : FunctorialComplexApproximation C where
  /-- Every term of every resolving complex is injective. -/
  injective (M : CochainComplex C ℤ) (n : ℤ) : Injective ((toFunctor.obj M).X n)
  /-- Every resolving complex is K-injective. -/
  isKInjective (M : CochainComplex C ℤ) : (toFunctor.obj M).IsKInjective

namespace Functorial

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Construct a functorial K-injective resolution from explicit approximation data and proofs. -/
def ofApproximation (J : FunctorialComplexApproximation C)
    (h_injective : ∀ (M : CochainComplex C ℤ) (n : ℤ),
      Injective ((J.toFunctor.obj M).X n))
    (h_isKInjective : ∀ (M : CochainComplex C ℤ),
      (J.toFunctor.obj M).IsKInjective) : Functorial C :=
  { toApproximation := J
    injective := h_injective
    isKInjective := h_isKInjective }

/-- The constructor preserves the approximation data and its injectivity properties. -/
theorem ofApproximation_spec (J : FunctorialComplexApproximation C)
    (h_injective : ∀ (M : CochainComplex C ℤ) (n : ℤ),
      Injective ((J.toFunctor.obj M).X n))
    (h_isKInjective : ∀ (M : CochainComplex C ℤ),
      (J.toFunctor.obj M).IsKInjective) :
    (∀ (M : CochainComplex C ℤ), Mono (J.ι.app M)) ∧
      (∀ (M : CochainComplex C ℤ), QuasiIso (J.ι.app M)) ∧
      (∀ (M : CochainComplex C ℤ) (n : ℤ),
        Injective (((ofApproximation J h_injective h_isKInjective).toFunctor.obj M).X n)) ∧
      ∀ (M : CochainComplex C ℤ),
        ((ofApproximation J h_injective h_isKInjective).toFunctor.obj M).IsKInjective := sorry

/-- The objectwise K-injective resolution supplied by a functorial resolution. -/
@[stacks 079P "objectwise K-injective resolution"]
def resolution (R : Functorial C) (M : CochainComplex C ℤ) :
    KInjectiveResolution M :=
  KInjectiveResolution.mk (R.toFunctor.obj M) (R.isKInjective M)
    (R.ι.app M) (R.quasiIso_app M)

/-- The resolving complex of `R.resolution M` is the value of the underlying approximation
functor at `M`. -/
@[stacks 079P "objectwise resolving complex", simp]
theorem resolution_complex (R : Functorial C) (M : CochainComplex C ℤ) :
    (R.resolution M).complex = R.toFunctor.obj M := sorry

/-- The comparison map of `R.resolution M` is the component of the functorial comparison. -/
@[stacks 079P "objectwise resolution comparison", simp]
theorem resolution_ι (R : Functorial C) (M : CochainComplex C ℤ) :
    (R.resolution M).ι = R.ι.app M := sorry

/-- The maps of the underlying approximation functor intertwine the objectwise resolution
comparisons. -/
@[stacks 079P "objectwise resolution naturality", reassoc (attr := simp)]
theorem resolution_naturality (R : Functorial C) {M N : CochainComplex C ℤ}
    (f : M ⟶ N) :
    (R.resolution M).ι ≫ R.toFunctor.map f = f ≫ (R.resolution N).ι := sorry

/-- Functorial K-injective resolutions exist in every Grothendieck abelian category. -/
@[stacks 079P "bundled existence"]
theorem nonempty [IsGrothendieckAbelian.{w} C] :
    Nonempty (Functorial C) := sorry

/-- The unbundled existential view of a functorial K-injective resolution. -/
@[stacks 079P "existential view"]
theorem exists_approximation [IsGrothendieckAbelian.{w} C] :
    ∃ J : FunctorialComplexApproximation C,
      (∀ (M : CochainComplex C ℤ) (n : ℤ), Injective ((J.toFunctor.obj M).X n)) ∧
        ∀ M : CochainComplex C ℤ, (J.toFunctor.obj M).IsKInjective := sorry

end Functorial
end KInjectiveResolution

end CochainComplex
