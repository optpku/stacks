/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.PropertyC
public import ReasLib.CategoryTheory.Sites.AlmostCocontinuous

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- If every étale base change of a scheme morphism has Property (C) and is
closed, its pullback functor on the small étale sites is almost cocontinuous. -/
theorem smallEtalePullback_isAlmostCocontinuous
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h_propertyC :
      ∀ V : Y.Etale,
        AlgebraicGeometry.Scheme.Etale.SmallToBig.hasPropertyC
          (pullback.snd f V.hom))
    (h_closed : ∀ V : Y.Etale, IsClosedMap (pullback.snd f V.hom).base) :
    Functor.IsAlmostCocontinuous (Scheme.smallEtalePullback f)
      Y.smallEtaleTopology X.smallEtaleTopology := sorry

end AlgebraicGeometry.Scheme
