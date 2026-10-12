/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.InjectiveResolution
public import ReasLib.CategoryTheory.DerivedCategory.Preimage.Homology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Injective models of bounded-below derived objects

An object in `D^{≥ a}` over an abelian category with enough injectives admits a cochain model
which is zero below the same bound and injective in every degree.  The model is returned in the
fixed-bound bundled category, so its support and termwise injectivity are immediately reusable.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory.IsGE

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
variable {K : DerivedCategory C}

/-- A cohomologically bounded-below derived object admits a termwise-injective model with the
same strict lower bound. -/
@[stacks 013K "derived fixed-bound injective model",
  stacks 0G21 "bounded-below injective model"]
theorem exists_injective_model [EnoughInjectives C] {a : ℤ} (hK : K.IsGE a) :
    ∃ I : CochainComplex.StrictlyGE.TermsIn (isInjective C) a,
      IsIsomorphic (DerivedCategory.Q.obj I.obj) K := sorry

end CategoryTheory.DerivedCategory.IsGE

end
