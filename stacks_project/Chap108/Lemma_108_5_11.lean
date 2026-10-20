module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.HilbertPower

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

universe u

/- Lemma 108.5.11: replacing an invertible module by a positive tensor power
replaces its globally polynomial Hilbert function `P` by `fun t ↦ P ((n : ℤ) * t)`
without changing the Hilbert subfunctor. -/
@[stacks 0DP8] #check (AlgebraicGeometry.AlgebraicSpace.Quot.quotHilbert_tensorPower :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [FinitePresentation f] [Separated f]
    (F : X.Modules) [F.IsQuasicoherent] (L : X.Modules) [isInvertibleObject L]
    (P : ℤ → ℤ)
    (hP : ∃ p : Polynomial ℚ, ∀ t : ℤ, p.eval (t : ℚ) = (P t : ℚ))
    (n : ℕ) (hn : 0 < n),
    AlgebraicGeometry.AlgebraicSpace.Quot.quotHilbert f F L P =
      AlgebraicGeometry.AlgebraicSpace.Quot.quotHilbert f F (tensorPower L n)
        (fun t ↦ P ((n : ℤ) * t)))
