module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.AlgebraicGeometry.Scheme.Limit.Preservation

/-!
# Sheafification preserves directed affine limits

If a set-valued functor on the big fppf site of schemes over `S` preserves
directed inverse limits of affines, then so does its fppf sheafification.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Over

/-- The plus construction preserves directed affine limits of a set-valued
presheaf on schemes over a fixed base scheme. -/
theorem plusObj_preservesDirectedAffineLimits {S : Scheme.{u}}
    (F : (Over S)ᵒᵖ ⥤ Type (u + 1))
    (hF : PreservesDirectedAffineLimits S F) :
    PreservesDirectedAffineLimits S ((Scheme.fppfTopology.over S).plusObj F) :=
  sorry

/-- Fppf sheafification preserves directed affine limits of a set-valued
presheaf on schemes over a fixed base scheme. -/
theorem sheafify_preservesDirectedAffineLimits {S : Scheme.{u}}
    (F : (Over S)ᵒᵖ ⥤ Type (u + 1))
    (hF : PreservesDirectedAffineLimits S F) :
    PreservesDirectedAffineLimits S ((Scheme.fppfTopology.over S).sheafify F) :=
  sorry

namespace IsLimitPreserving

/-- The plus construction preserves limit-preserving natural transformations
of set-valued functors on the big fppf site over a scheme. -/
theorem plusMap {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type (u + 1)} {a : F ⟶ G}
    (ha : IsLimitPreserving a) :
    IsLimitPreserving ((Scheme.fppfTopology.over S).plusMap a) :=
  sorry

/-- Fppf sheafification preserves limit-preserving natural transformations of
set-valued functors on the big fppf site over a scheme. -/
theorem sheafifyMap {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type (u + 1)} {a : F ⟶ G}
    (ha : IsLimitPreserving a) :
    IsLimitPreserving ((Scheme.fppfTopology.over S).sheafifyMap a) :=
  sorry

end IsLimitPreserving

end AlgebraicGeometry.Scheme.Over
