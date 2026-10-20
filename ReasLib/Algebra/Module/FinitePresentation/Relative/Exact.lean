/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.FinitePresentation.Exact
public import ReasLib.Algebra.Module.FinitePresentation.Relative.Presentation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative finite presentation in short exact sequences

Relative finite presentation has the expected extension and quotient closure properties.
-/

@[expose] public section

universe u v w x y

namespace Module

variable {R : Type u} {A : Type v}
variable {M' : Type w} {M : Type x} {M'' : Type y}
variable [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
variable [AddCommGroup M'] [Module A M']
variable [AddCommGroup M] [Module A M]
variable [AddCommGroup M''] [Module A M'']

/-- In a short exact sequence, relative finite presentation of
the outer terms implies relative finite presentation of the middle term. -/
@[stacks 0671 "relative finite presentation is closed under extensions"]
theorem finitePresentationRelativeTo_of_shortExact
    (f : M' →ₗ[A] M) (g : M →ₗ[A] M'')
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (hM' : FinitePresentationRelativeTo R A M')
    (hM'' : FinitePresentationRelativeTo R A M'') :
    FinitePresentationRelativeTo R A M := sorry
/- Proof strategy: use `iff_overEveryPolynomialPresentation` and fix a surjective polynomial
presentation of `A`; restrict the short exact sequence along that map, obtain finite presentation
of both outer terms from `hM'` and `hM''`, and apply `Module.finitePresentation_of_exact`. -/

/-- In a short exact sequence, a finite left term and a relatively
finitely presented middle term imply relative finite presentation of the quotient. -/
@[stacks 0671 "relative finite presentation of a quotient in a short exact sequence"]
theorem finitePresentationRelativeTo_quotient_of_shortExact
    (f : M' →ₗ[A] M) (g : M →ₗ[A] M'')
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (hM'_finite : Module.Finite A M') (hM : FinitePresentationRelativeTo R A M) :
    FinitePresentationRelativeTo R A M'' := sorry
/- Proof strategy: test against every surjective polynomial presentation of `A`; finite
generation of `M'` survives restriction of scalars along the surjection, while `hM` supplies
finite presentation of `M`; apply `Module.finitePresentation_of_surjective_of_exact` and package
the resulting family with `iff_overEveryPolynomialPresentation`. -/

end Module
