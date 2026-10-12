/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.Algebra.Homology.DerivedCategory.InjectiveAmplitude.Ext
public import ReasLib.CategoryTheory.DerivedCategory.Bounded.Homology

@[expose] public section

/-!
# Finite injective dimension over Noetherian rings

This leaf packages the Noetherian devissage criterion at the derived-object level.  The
bounded-below hypothesis is carried by `DerivedCategory.Plus`, and vanishing is expressed by
`Subsingleton` rather than by quantifying over individual extension classes.

@stack 0DW2
-/

noncomputable section

universe u

open CategoryTheory
open scoped DerivedExt

namespace CategoryTheory.DerivedCategory.HasFiniteInjectiveDimension

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- Lemma 15.70.6, Stacks `0DW2`: a bounded-below complex with finite cohomology has finite
injective dimension exactly when high derived extensions from all `R ⧸ J`, for `J` above a
fixed ideal in the Jacobson radical, vanish. -/
@[stacks 0DW2 "Noetherian ideal-quotient criterion"]
theorem iff_eventually_idealQuotient_ext
    (K : DerivedCategory.Plus (ModuleCat R))
    (I : Ideal R) (hI : I ≤ Ring.jacobson R)
    (hKfinite : ∀ i : ℤ,
      Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj K.obj)) :
    HasFiniteInjectiveDimension K.obj ↔
      ∃ b : ℤ, ∀ J : Ideal R, I ≤ J → ∀ i : ℤ, b < i →
        Subsingleton
          (Ext⁽i⁾((DerivedCategory.singleFunctor (ModuleCat R) 0).obj
            (ModuleCat.of R (R ⧸ J)), K.obj)) := sorry

end CategoryTheory.DerivedCategory.HasFiniteInjectiveDimension
