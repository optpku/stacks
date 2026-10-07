module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.DeRham.CupProduct

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory ComplexShape
open DerivedCategory.DerivedTensor.Right.Monoidal

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

variable {X S : Scheme.{u}}

/- Lemma 50.4.1: For every morphism of schemes, the cup product on relative de Rham cohomology
is associative and graded commutative. -/
@[stacks 0FM3] #check (AlgebraicGeometry.Scheme.DeRham.cohomologyCupProduct_assoc :
  (p : X ⟶ S) →
  [MonoidalCategory (coefficientDerived p)] →
  [(DerivedCategory.Qh : HomotopyCategory (coefficientModules p) (up ℤ) ⥤
    coefficientDerived p).Monoidal] →
  [(globalDerivedFunctor p).LaxMonoidal] →
  (i j k : ℤ) →
    (cohomologyCupProduct p i j ▷ cohomology p k) ≫
        cohomologyCupProduct p (i + j) k =
      (α_ (cohomology p i) (cohomology p j) (cohomology p k)).hom ≫
        (cohomology p i ◁ cohomologyCupProduct p j k) ≫
        cohomologyCupProduct p i (j + k) ≫
        eqToHom (congrArg (cohomology p) (add_assoc i j k).symm))

#check (AlgebraicGeometry.Scheme.DeRham.cohomologyCupProduct_gradedComm :
  (p : X ⟶ S) →
  [MonoidalCategory (coefficientDerived p)] → [BraidedCategory (coefficientDerived p)] →
  [(DerivedCategory.Qh : HomotopyCategory (coefficientModules p) (up ℤ) ⥤
    coefficientDerived p).Braided] →
  [(globalDerivedFunctor p).LaxBraided] →
  (i j : ℤ) →
    cohomologyCupProduct p i j =
      (i * j).negOnePow •
        ((β_ (cohomology p i) (cohomology p j)).hom ≫
          cohomologyCupProduct p j i ≫
          eqToHom (congrArg (cohomology p) (add_comm j i))))

end AlgebraicGeometry.Scheme.DeRham
