module

public import ReasLib.RingTheory.Ideal.GoingUpDown.Polynomial
public import ReasLib.RingTheory.Ideal.GoingUpDown.Localization
public import ReasLib.RingTheory.Ideal.GoingUpDown.Parabola
public import ReasLib.RingTheory.Ideal.GoingUpDown.SplitLine
import StacksCheckRecall
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

noncomputable section

open PrimeSpectrum Polynomial Localization
open scoped Polynomial.Bivariate

universe u

/- Exercise 111.24.2 (1): going up holds for `k → k[X]`, i.e. `Spec(k[X]) → Spec(k)` is a
specializing map. -/
@[stacks 02DY] #check
  (@GoingUpDown.Polynomial.specializingMap_comap_polynomialOverField :
    ∀ {k : Type u} [Field k], SpecializingMap (comap (algebraMap k k[X])))

/- Exercise 111.24.2 (2): going down holds for `k → k[X]`. -/
@[stacks 02DY] #check
  (GoingUpDown.Polynomial.hasGoingDown_polynomialOverField :
    ∀ {k : Type u} [Field k], Algebra.HasGoingDown k k[X])

/- Exercise 111.24.2 (3): going up fails for `k[X] → k[X][Y]`. -/
@[stacks 02DY] #check
  (GoingUpDown.Polynomial.not_specializingMap_comap_bivariateOverPolynomial :
    ∀ {k : Type u} [Field k], ¬ SpecializingMap (comap (algebraMap k[X] k[X][Y])))

/- Exercise 111.24.2 (4): going down holds for `k[X] → k[X][Y]`. -/
@[stacks 02DY] #check
  (GoingUpDown.Polynomial.hasGoingDown_bivariateOverPolynomial :
    ∀ {k : Type u} [Field k], Algebra.HasGoingDown k[X] k[X][Y])

/- Exercise 111.24.2 (5): going up fails for `ℤ → Away (11 : ℤ)`. -/
@[stacks 02DY] #check
  (GoingUpDown.Localization.not_specializingMap_comap_awayEleven :
    ¬ SpecializingMap (comap (algebraMap ℤ (Away (11 : ℤ)))))

/- Exercise 111.24.2 (6): going down holds for `ℤ → Away (11 : ℤ)`. -/
@[stacks 02DY] #check
  (GoingUpDown.Localization.hasGoingDown_awayEleven :
    Algebra.HasGoingDown ℤ (Away (11 : ℤ)))

/- Exercise 111.24.2 (7): going up holds for
`algebraMap (MvPolynomial (Fin 2) k) (parabolaAdjoin k)`. -/
@[stacks 02DY] #check
  (@GoingUpDown.Parabola.specializingMap_comap_parabolaAdjoin :
    ∀ {k : Type u} [Field k] [IsAlgClosed k],
      SpecializingMap
        (comap (algebraMap (MvPolynomial (Fin 2) k)
          (GoingUpDown.Parabola.parabolaAdjoin k))))

/- Exercise 111.24.2 (8): going down fails for
`algebraMap (MvPolynomial (Fin 2) k) (parabolaAdjoin k)`. -/
@[stacks 02DY] #check
  (GoingUpDown.Parabola.not_hasGoingDown_parabolaAdjoin :
    ∀ {k : Type u} [Field k] [IsAlgClosed k],
      ¬ Algebra.HasGoingDown (MvPolynomial (Fin 2) k)
        (GoingUpDown.Parabola.parabolaAdjoin k))

/- Exercise 111.24.2 (9): going up holds for `ℤ → Away (⟨2, 1⟩ : GaussianInt)`. -/
@[stacks 02DY] #check
  (GoingUpDown.Localization.specializingMap_comap_gaussianAway_twoPlusI :
    SpecializingMap (comap (algebraMap ℤ (Away (⟨2, 1⟩ : GaussianInt)))))

/- Exercise 111.24.2 (10): going down holds for `ℤ → Away (⟨2, 1⟩ : GaussianInt)`. -/
@[stacks 02DY] #check
  (GoingUpDown.Localization.hasGoingDown_gaussianAway_twoPlusI :
    Algebra.HasGoingDown ℤ (Away (⟨2, 1⟩ : GaussianInt)))

/- Exercise 111.24.2 (11): going up fails for `ℤ → Away (⟨14, 7⟩ : GaussianInt)`. -/
@[stacks 02DY] #check
  (GoingUpDown.Localization.not_specializingMap_comap_gaussianAway_fourteenPlusSevenI :
    ¬ SpecializingMap (comap (algebraMap ℤ (Away (⟨14, 7⟩ : GaussianInt)))))

/- Exercise 111.24.2 (12): going down holds for `ℤ → Away (⟨14, 7⟩ : GaussianInt)`. -/
@[stacks 02DY] #check
  (GoingUpDown.Localization.hasGoingDown_gaussianAway_fourteenPlusSevenI :
    Algebra.HasGoingDown ℤ (Away (⟨14, 7⟩ : GaussianInt)))

/- Exercise 111.24.2 (13): going up fails for `algebraMap k[X] (splitLineAway k)`. -/
@[stacks 02DY] #check
  (GoingUpDown.SplitLine.not_specializingMap_comap_splitLineAway :
    ∀ {k : Type u} [Field k] [IsAlgClosed k],
      ¬ SpecializingMap
        (comap (algebraMap k[X] (GoingUpDown.SplitLine.splitLineAway k))))

/- Exercise 111.24.2 (14): going down holds for `algebraMap k[X] (splitLineAway k)`. -/
@[stacks 02DY] #check
  (GoingUpDown.SplitLine.hasGoingDown_splitLineAway :
    ∀ {k : Type u} [Field k] [IsAlgClosed k],
      Algebra.HasGoingDown k[X] (GoingUpDown.SplitLine.splitLineAway k))
