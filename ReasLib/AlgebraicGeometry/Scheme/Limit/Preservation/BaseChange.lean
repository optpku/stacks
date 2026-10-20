module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.Preservation
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Base change of limit-preserving transformations

A limit-preserving transformation of functors on schemes over a base remains
limit preserving after arbitrary base change along a fibre-product square.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry Limits

universe u v

namespace AlgebraicGeometry.Scheme.Over.IsLimitPreserving

/-- In a pullback square of set-valued functors on schemes over a base, the
base change of a limit-preserving natural transformation is limit preserving. -/
theorem of_isPullback {S : Scheme.{u}} {F G H P : (Over S)ᵒᵖ ⥤ Type v}
    {a : F ⟶ G} {b : H ⟶ G} {a' : P ⟶ H} {b' : P ⟶ F}
    (sq : IsPullback b' a' a b) (ha : IsLimitPreserving a) :
    IsLimitPreserving a' := sorry

/-- The chosen base-change projection `pullback.snd a b` of a limit-preserving
transformation `a : F ⟶ G` along `b : H ⟶ G` is limit preserving. -/
theorem pullback_snd {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type v} {a : F ⟶ G}
    (ha : IsLimitPreserving a) (b : H ⟶ G) [HasPullback a b] :
    IsLimitPreserving (pullback.snd a b) := by
  apply of_isPullback (IsPullback.of_hasPullback a b)
  sorry

end AlgebraicGeometry.Scheme.Over.IsLimitPreserving
