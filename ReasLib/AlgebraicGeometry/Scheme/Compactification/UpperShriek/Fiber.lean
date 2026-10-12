/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.Dualizing
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.ProjectionFormula
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.FlatBaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Locality

@[expose] public section

open CategoryTheory
open DerivedCategory.Plus.CohomologyIn
open RingedSpace
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Scheme.Compactification

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Compactification
namespace Of
namespace UpperShriek

/-- For a flat finite-type separated morphism over a Noetherian scheme, the
derived pullback of its compactification upper-shriek dualizing object to any
scheme-theoretic fibre is dualizing on that fibre. -/
theorem fiberPullback_isDualizingComplex
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y) [Flat f.hom.left]
    (P : Of Y.obj.left (Over.mk f.hom.left))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P)) (y : Y.obj.left) :
    IsDualizingComplex
      ((DerivedQCoh.pullback (Scheme.Hom.fiberι f.hom.left y)).obj
        (dualizingObject f P A)).obj := sorry

end UpperShriek
end Of
end Compactification
end Scheme
end AlgebraicGeometry
