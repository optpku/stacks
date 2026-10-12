/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek
public import ReasLib.AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver.AffineLine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback.Flat

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

namespace AlgebraicGeometry.Scheme.Compactification.Of

/-- For the relative affine-line projection, a supplied bounded-below
upper-shriek model is noncanonically naturally isomorphic to flat pullback
followed by shift by one. -/
theorem upperShriek_affineLine_isomorphic
    {S : Scheme.{u}} [IsNoetherian S] (Y : FiniteTypeSeparatedOver S)
    (P : Of Y.obj.left
      (Over.mk (affineLineProjection Y).hom.left))
    (a : DerivedQCoh Y.obj.left ⥤ DerivedQCoh (P.obj.right).left)
    (aAdjunction : DerivedQCoh.pushforwardCohomologyIn P.obj.right.hom ⊣ a)
    (aPlus : DerivedQCoh.Plus Y.obj.left ⥤ DerivedQCoh.Plus (P.obj.right).left)
    (aPlusCompatibility :
      aPlus ⋙ ambient
          (quasiCoherentModuleProperty (P.obj.right).left) ≅
        toUnbounded (quasiCoherentModuleProperty Y.obj.left) ⋙
          a ⋙ DerivedQCoh.inclusion (P.obj.right).left) :
    IsIsomorphic
      (upperShriek (affineLineProjection Y) P aPlus)
      (pullbackPlus (affineLineProjection Y).hom.left ⋙
        shiftFunctor (DerivedQCoh.Plus (affineLine Y).obj.left) (1 : ℤ)) := sorry

end AlgebraicGeometry.Scheme.Compactification.Of
