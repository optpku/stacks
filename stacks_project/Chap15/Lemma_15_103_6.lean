/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Localization.Away

/-!
# Lemma 15.103.6

@stack 0H84
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open DerivedCategory

universe u

/- Lemma 15.103.6 (0H84): for the distinguished triangle given by multiplication by `f`,
localized negative homology of `M` and a lower bound on the cone force `M` to have no negative
homology.  The reusable owner is the arbitrary-cutoff `IsGE` criterion in
`DerivedCategory.LocalizationAway`; the displayed source conclusion is recovered through the
canonical `DerivedCategory.isGE_iff` bridge. -/

@[stacks 0H84 "Lemma 15.103.6"]
#check fun {R : Type u} [CommRing R]
    {M C : DerivedCategory (ModuleCat R)} {f : R}
    {g : M ⟶ C} {δ : C ⟶ M⟦(1 : ℤ)⟧}
    (hT : Triangle.mk (f • 𝟙 M) g δ ∈ distTriang (DerivedCategory (ModuleCat R)))
    (hMloc : ∀ i : ℤ, i < 0 →
      IsZero (ModuleCat.of (Localization.Away f)
        (LocalizedModule.Away f ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj M))))
    (hC : C.IsGE (-1)) ↦
  (DerivedCategory.isGE_iff M 0).1
    (DerivedCategory.LocalizationAway.isGE_zero_of_smul_cone
      (hT := hT) (hAway := hMloc) (hX := hC))

#check @DerivedCategory.LocalizationAway.homology
#check @DerivedCategory.LocalizationAway.isGE_of_smul_cone
#check @DerivedCategory.LocalizationAway.isGE_zero_of_smul_cone
