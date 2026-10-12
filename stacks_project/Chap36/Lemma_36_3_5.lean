/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Affine
import stacks_project.Chap36.«36_3_5_1»

open AlgebraicGeometry CategoryTheory

universe u

section

variable (A : CommRingCat.{u})

/- Lemma 36.3.5 (1): for `X = Spec A`, the comparison
`D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)` is a triangulated equivalence. -/
@[stacks 06Z0] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.affineComparisonIsEquivalence A :
    Functor.IsEquivalence
      (AlgebraicGeometry.Scheme.DerivedQCoh.comparison (Spec A)))

#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.affineComparisonIsTriangulated A :
    (AlgebraicGeometry.Scheme.DerivedQCoh.comparison (Spec A)).IsTriangulated)

/- Lemma 36.3.5 (2): for `X = Spec A`, derived global sections
`RΓ(X, -) : D_QCoh(𝒪_X) ⥤ D(A)` are a triangulated equivalence. -/
@[stacks 06Z0] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.affineGlobalSectionsIsEquivalence A :
    Functor.IsEquivalence
      (AlgebraicGeometry.Scheme.DerivedQCoh.affineGlobalSections A))

#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.affineGlobalSectionsIsTriangulated A :
    (AlgebraicGeometry.Scheme.DerivedQCoh.affineGlobalSections A).IsTriangulated)

/- Lemma 36.3.5 (3): for `X = Spec A`, the derived tilde functor
`D(A) ⥤ D(QCoh(𝒪_X))` is a triangulated equivalence. -/
@[stacks 06Z0] #check
  (CategoryTheory.Equivalence.mapDerivedCategory
      (AlgebraicGeometry.tildeEquiv :
        ModuleCat A ≌ AlgebraicGeometry.Scheme.QCoh (Spec A)) :
    DerivedCategory (ModuleCat A) ≌
      DerivedCategory (AlgebraicGeometry.Scheme.QCoh (Spec A)))

#check
  (inferInstance :
    (CategoryTheory.Equivalence.MapDerivedCategory.forwardExact
      (AlgebraicGeometry.tildeEquiv :
        ModuleCat A ≌ AlgebraicGeometry.Scheme.QCoh (Spec A))).mapDerivedCategory.IsTriangulated)

/- Lemma 36.3.5 (4): for `E : D_QCoh(𝒪_X)`, the object `H⁰(X, E)` is isomorphic
to the global sections of the cohomology sheaf `H⁰(E)`. -/
@[stacks 06Z0] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.affineGlobalSections_homologyZero A :
    (E : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty (Spec A).toRingedSpace)) →
      IsIsomorphic
        ((DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
          ((AlgebraicGeometry.Scheme.DerivedQCoh.affineGlobalSections A).obj E))
        ((AlgebraicGeometry.moduleSpecΓFunctor : (Spec A).Modules ⥤ ModuleCat A).obj
          (RingedSpace.ModuleDerived.cohomologySheaf E.obj 0)))

end
