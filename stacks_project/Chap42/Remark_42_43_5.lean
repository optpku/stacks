module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernPolynomial.Endomorphism

@[expose] public section

open CategoryTheory
open scoped MonoidalCategory

universe u

/- Remark 42.43.5 (1): A weighted-homogeneous polynomial in the rank and Chern
classes of a finite locally free module determines a class of the corresponding
degree. -/
@[stacks 0FA7] #check
  (AlgebraicGeometry.ChernPolynomial.homogeneousValue_spec :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
      [AlgebraicGeometry.UniversallyCatenary S] [IsDimensionFunction δ]
      [AlgebraicGeometry.LocallyOfFiniteType p]
      (classes : AlgebraicGeometry.ChernClass.Theory δ p) (E : X.Modules)
      [E.IsFiniteLocallyFree] (P : MvPolynomial ℕ ℤ) (n : ℕ)
      (hP : MvPolynomial.IsWeightedHomogeneous id P n),
      AlgebraicGeometry.ChernClass.homogeneous δ p n
          (AlgebraicGeometry.ChernPolynomial.homogeneousValue
            δ p classes E P n hP) =
        (AlgebraicGeometry.ChernPolynomial.eval δ p classes E P).1)

/- Remark 42.43.5 (2): For a finite locally free module `E`, the second Chern
class of its endomorphism module `E ⊗ Scheme.Modules.dual E` is obtained by
evaluating `2 * r * c₂ - (r - 1) * c₁ ^ 2`. -/
@[stacks 0FA7] #check
  (AlgebraicGeometry.ChernClass.Theory.component_endomorphism_two :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
      [AlgebraicGeometry.UniversallyCatenary S] [IsDimensionFunction δ]
      [AlgebraicGeometry.LocallyOfFiniteType p]
      (classes : AlgebraicGeometry.ChernClass.Theory δ p) (E : X.Modules)
      [E.IsFiniteLocallyFree],
      classes.component
          (E ⊗ AlgebraicGeometry.Scheme.Modules.dual E) 2 =
        AlgebraicGeometry.ChernPolynomial.homogeneousValue δ p classes E
          AlgebraicGeometry.ChernPolynomial.endomorphism 2
            AlgebraicGeometry.ChernPolynomial.endomorphism_isWeightedHomogeneous)
