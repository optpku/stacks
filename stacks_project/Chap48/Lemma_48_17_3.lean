/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.AffineLine
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.StructuredArrow
open DerivedCategory.Plus.CohomologyIn
open RingedSpace
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Compactification
open AlgebraicGeometry.Scheme.Compactification.Of
open AlgebraicGeometry.Scheme.DerivedQCoh.Flat
open AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver

noncomputable section

universe u

/- Lemma 48.17.3: for the projection from the affine line over `Y` to `Y`, any valid
bounded-below upper-shriek model is noncanonically naturally isomorphic to bounded-below
derived pullback followed by the shift `[1]`. -/
@[stacks 0AA1] #check
  (AlgebraicGeometry.Scheme.Compactification.Of.upperShriek_affineLine_isomorphic :
    ∀ {S : Scheme.{u}} [IsNoetherian S] (Y : FiniteTypeSeparatedOver S)
      (P : Of Y.obj.left
        (Over.mk (affineLineProjection Y).hom.left))
      (a : DerivedQCoh Y.obj.left ⥤ DerivedQCoh (P.obj.right).left)
      (aAdjunction : DerivedQCoh.pushforwardCohomologyIn P.obj.right.hom ⊣ a)
      (aPlus : DerivedQCoh.Plus Y.obj.left ⥤ DerivedQCoh.Plus (P.obj.right).left)
      (aPlusCompatibility :
        aPlus ⋙ ambient
            (quasiCoherentModuleProperty (P.obj.right).left) ≅
          toUnbounded (quasiCoherentModuleProperty Y.obj.left) ⋙
            a ⋙ DerivedQCoh.inclusion (P.obj.right).left),
      IsIsomorphic
        (upperShriek (affineLineProjection Y) P aPlus)
        (pullbackPlus (affineLineProjection Y).hom.left ⋙
          shiftFunctor (DerivedQCoh.Plus (affineLine Y).obj.left) (1 : ℤ)))
