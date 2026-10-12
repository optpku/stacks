/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.FiberDimension
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.RingedSpace.ModuleDerived

universe u

/- Lemma 48.21.3: If the degree-`i` cohomology stalk at `x` of the compactification
model of `f⁺!𝒪_Y` is nontrivial, then `-(d : ℤ) ≤ i`, where `d` is the local dimension
at `x` of the fibre of `f` over `f x`. -/
@[stacks 0BV5] #check
  (AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek.neg_fiberDimension_le_of_cohomologyStalk_nontrivial :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} [hS : AlgebraicGeometry.IsNoetherian S]
      {X Y : AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver S}
      (f : X ⟶ Y)
      (P : AlgebraicGeometry.Scheme.Compactification.Of Y.obj.left (Over.mk f.hom.left))
      (A : AlgebraicGeometry.Scheme.DerivedQCoh.PlusRightAdjoint
        (AlgebraicGeometry.Scheme.Compactification.Of.ambientMorphism P))
      (x : X.obj.left) (d : ℕ),
      AlgebraicGeometry.Scheme.Hom.fiberDimensionAt f.hom.left x = (d : WithBot ℕ∞) →
      ∀ i : ℤ,
      Nontrivial
        (AlgebraicGeometry.RingedSpace.ModuleDerived.cohomologyStalk
          (AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek.dualizingObject f P A).obj
          i x) →
      -(d : ℤ) ≤ i)
