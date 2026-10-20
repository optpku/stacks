/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.TheoremOfCube
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry
namespace Scheme
namespace Modules
namespace Invertible

/- Theorem 37.33.8 (Theorem of the cube): an invertible module on
`X ×[S] Y ×[S] Z` is trivial if its two section-face restrictions and one
`Z`-fibre restriction are trivial, under the stated geometric hypotheses. -/
@[stacks 0BF4] #check
  (AlgebraicGeometry.Scheme.Modules.Invertible.isTrivial_of_cube :
    ∀ {X Y Z S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (k : Z ⟶ S)
      [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f]
      [GeometricallyIntegral f] [Flat g] [IsProper g]
      [Scheme.Hom.FinitePresentation g] [GeometricallyIntegral g] [ConnectedSpace Z]
      (x : SplitEpi f) (y : SplitEpi g) (z : Z)
      (L : (CategoryTheory.Limits.pullback (pullback.fst f g ≫ f) k).Modules)
      [Invertible L]
      (h_first : RingedSpace.IsTrivial
        ((Scheme.Modules.pullback (TripleProduct.firstSection f g k x)).obj L))
      (h_second : RingedSpace.IsTrivial
        ((Scheme.Modules.pullback (TripleProduct.secondSection f g k y)).obj L))
      (h_fibre : RingedSpace.IsTrivial
        ((Scheme.Modules.pullback
          ((pullback.snd (pullback.fst f g ≫ f) k).fiberι z)).obj L)),
      RingedSpace.IsTrivial L)

end Invertible
end Modules
end Scheme
end AlgebraicGeometry
