module

public import ReasLib.AlgebraicGeometry.QCohStack.StronglyCartesian
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 95.4.1: a morphism `(f, φ) : (Y, G) ⟶ (X, F)` of `QCohStack` is
strongly cartesian if and only if `φ` induces an isomorphism `f* F ⟶ G`. -/
@[stacks 04U3] #check (AlgebraicGeometry.QCohStack.isStronglyCartesian_iff_isIso_sheaf :
  ∀ {S : Scheme.{u}} {x y : AlgebraicGeometry.QCohStack.Obj S} (φ : x ⟶ y),
    (AlgebraicGeometry.QCohStack.p S).IsStronglyCartesian
      ((AlgebraicGeometry.QCohStack.p S).map φ) φ ↔ IsIso φ.sheaf)
