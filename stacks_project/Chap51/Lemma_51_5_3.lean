/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.ClosedSupport

@[expose] public section

open CategoryTheory CategoryTheory.Limits Set

noncomputable section

universe u

/- Lemma 51.5.3: for a specialization-stable subset `T ⊆ Spec(A)`, cohomology of
derived sections supported on `T` is the filtered colimit of cohomology with closed support
`Z ⊆ T`. -/
@[stacks 0EF1] #check (CategoryTheory.ModuleCat.SupportedOn.comparisonIsIso :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ),
    IsIso (ModuleCat.SupportedOn.comparison T hT K i))
