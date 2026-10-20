module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.Preservation.Sheafification
import StacksCheckRecall

/-!
# Sheafification preserves directed affine limits

If a set-valued functor on the big fppf site of schemes over `S` preserves
directed inverse limits of affines, then so does its fppf sheafification.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Over

/- Lemma 70.3.7: let `S` be a scheme contained in `Sch_fppf`, and let
`F : (Over S)ᵒᵖ ⥤ Type (u + 1)` be a functor on `(Sch/S)_fppf`. If `F` is
limit preserving, then its fppf sheafification
`(Scheme.fppfTopology.over S).sheafify F` is limit preserving. -/
@[stacks 049O] #check
  (AlgebraicGeometry.Scheme.Over.sheafify_preservesDirectedAffineLimits :
    ∀ {S : Scheme.{u}}
    (F : (Over S)ᵒᵖ ⥤ Type (u + 1))
    (hF : PreservesDirectedAffineLimits S F),
      PreservesDirectedAffineLimits S ((Scheme.fppfTopology.over S).sheafify F))

#check
  (AlgebraicGeometry.Scheme.Over.plusObj_preservesDirectedAffineLimits :
    ∀ {S : Scheme.{u}}
    (F : (Over S)ᵒᵖ ⥤ Type (u + 1))
    (hF : PreservesDirectedAffineLimits S F),
      PreservesDirectedAffineLimits S ((Scheme.fppfTopology.over S).plusObj F))

end AlgebraicGeometry.Scheme.Over
