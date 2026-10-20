module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.V.Over
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open Scheme.Over

universe u v w

/- Lemma 61.10.3: if a contravariant functor on all schemes over a scheme `S`
is an h-sheaf and preserves directed affine limits, then it satisfies the
sheaf property for the V topology. -/
@[stacks 0EVQ] #check
  (AlgebraicGeometry.Scheme.Over.satisfiesVSheafProperty_of_isHSheaf_of_preservesDirectedAffineLimits :
    ∀ {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type v),
      Presheaf.IsSheaf ((Scheme.hPrecoverage.toGrothendieck).over S) F →
        PreservesDirectedAffineLimits S F →
          satisfiesVSheafProperty.{u, v, w} S F)
