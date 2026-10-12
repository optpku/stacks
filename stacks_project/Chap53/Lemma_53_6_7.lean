/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Curve.GlobalGeneration
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.DerivedQCoh
open AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex
open Scheme.Modules
open CategoryTheory.MonoidalCategory

universe u

/- Lemma 53.6.7: in Situation 53.6.2, if `L` is a relatively very ample
invertible module of degree at least two, then `curveDualizingModule X.hom ⊗ L`
is globally generated. -/
@[stacks 0B5H]
#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.tensor_isGloballyGenerated_of_relativelyVeryAmple :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
      (h_dimension : topologicalKrullDim X.left = 1)
      (hΓ : Function.Bijective (Hom.globalSectionsMap X.hom))
      (L : X.left.Modules) [Invertible L]
      (h_veryAmple : RelativelyVeryAmple X.hom L)
      (h_degree : 2 ≤ curveDegreeOfInvertible X.hom h_dimension.le L),
      SheafOfModules.IsGloballyGenerated (curveDualizingModule X.hom ⊗ L))
