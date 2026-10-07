module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Cohomology

@[expose] public section

/-!
# Lemma 15.98.6 (Kollár-Kovács)

@stack 0EGS
-/

open CategoryTheory

/- Lemma 15.98.6 (Kollár-Kovács) (0EGS): the limit of the cohomology quotient system agrees with
the limit of the cohomology of the ideal-power derived tensor system.  ReasLib exposes the
degreewise theorem with only the preceding Mittag-Leffler hypothesis. -/
@[stacks 0EGS "Kollár-Kovács comparison of ideal-power cohomology limits"]
#check fun {A : Type*} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (K : DerivedCategory (ModuleCat A))
    (hKfinite : ∀ j : ℤ,
      Module.Finite A
        ((DerivedCategory.homologyFunctor (ModuleCat A) j).obj K))
    (hML : ∀ j : ℤ,
      (DerivedCategory.IdealPower.homologySystem I K j).IsMittagLeffler)
    (i : ℤ) ↦
  DerivedCategory.IdealPower.HomologySystem.quotientLimit
    I K i hKfinite (hML (i - 1))

#check @DerivedCategory.IdealPower.HomologySystem.adicLimit
