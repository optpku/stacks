/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import ReasLib.Algebra.Homology.ShortComplex.UniversallyExact
public import ReasLib.LinearAlgebra.TensorProduct.Pi.FinitePresentation
public import ReasLib.RingTheory.Flatness.MittagLeffler.TensorProduct

/-!
# Mittag-Leffler modules in exact sequences

This file records the three standard propagation directions for the Mittag-Leffler property in
short exact sequences.  The universally exact directions are kept separate from the finite-kernel
quotient direction because they use different hypotheses.
-/

@[expose] public section

universe u v

namespace Module.MittagLeffler

variable {R : Type u} [CommRing R]
variable {K M C : Type v}
variable [AddCommGroup K] [Module R K]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup C] [Module R C]

/-- A universally injective submodule of a Mittag-Leffler module is Mittag-Leffler. -/
theorem of_universallyInjective [MittagLeffler R M] (f : K →ₗ[R] M)
    (hf : LinearMap.UniversallyInjective.{u, v, v, v} f) :
    MittagLeffler R K := sorry

/-- The middle term of an exact sequence is Mittag-Leffler when both endpoints are
Mittag-Leffler and the left map is universally injective. -/
theorem of_exact [MittagLeffler R K] [MittagLeffler R C]
    (f : K →ₗ[R] M) (g : M →ₗ[R] C) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) (hf : LinearMap.UniversallyInjective.{u, v, v, v} f) :
    MittagLeffler R M := sorry

end Module.MittagLeffler

namespace CategoryTheory.ShortComplex

open CategoryTheory

variable {R : Type u} [CommRing R]
variable {S : ShortComplex (ModuleCat.{v} R)}

namespace UniversallyExact

/-- Lemma 10.89.7 (1), tag `059N`: in a universally exact short complex, a Mittag-Leffler
middle term forces the left term to be Mittag-Leffler. -/
@[stacks 059N "(1)"]
theorem mittagLeffler_X₁ [Module.MittagLeffler R S.X₂] (hS : UniversallyExact S) :
    Module.MittagLeffler R S.X₁ := sorry

/-- Lemma 10.89.7 (2), tag `059N`: in a universally exact short complex, Mittag-Leffler
endpoints force the middle term to be Mittag-Leffler. -/
@[stacks 059N "(2)"]
theorem mittagLeffler_X₂ [Module.MittagLeffler R S.X₁]
    [Module.MittagLeffler R S.X₃] (hS : UniversallyExact S) :
    Module.MittagLeffler R S.X₂ := sorry

end UniversallyExact

/-- Lemma 10.89.8, tag `0EGI`: the quotient in an exact, right-surjective short complex is
Mittag-Leffler when the kernel term is finite and the middle term is Mittag-Leffler. -/
@[stacks 0EGI]
theorem mittagLeffler_X₃_of_exact_of_finite_of_mittagLeffler
    (hS : S.Exact) (hSurj : Function.Surjective S.g) [Module.Finite R S.X₁]
    [Module.MittagLeffler R S.X₂] : Module.MittagLeffler R S.X₃ := sorry

end CategoryTheory.ShortComplex
