module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Tensor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Hilbert

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

universe u

/- Lemma 108.5.10 (1): tensoring with an invertible module identifies the Quot functors. -/
@[stacks 0DP7] #check (AlgebraicGeometry.AlgebraicSpace.Quot.tensorIso :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [FinitePresentation f] [Separated f] (F L : X.Modules)
    [F.IsQuasicoherent] [isInvertibleObject L],
    AlgebraicGeometry.AlgebraicSpace.Quot.quot f F ≅
      AlgebraicGeometry.AlgebraicSpace.Quot.quot f (F ⊗ L))

/- Lemma 108.5.10 (2): tensoring identifies the open and closed Hilbert loci for
P and fun t ↦ P (t + 1). -/
@[stacks 0DP7] #check (AlgebraicGeometry.AlgebraicSpace.Quot.tensorIso_hilbert :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [FinitePresentation f] [Separated f] (F L : X.Modules)
    [F.IsQuasicoherent] [isInvertibleObject L] (P : ℤ → ℤ)
    (hP : IsNumericalPolynomial P),
    (AlgebraicGeometry.AlgebraicSpace.Quot.quotHilbert f F L P).toFunctor ≅
      (AlgebraicGeometry.AlgebraicSpace.Quot.quotHilbert f (F ⊗ L) L
        (fun t ↦ P (t + 1))).toFunctor)
