module

public import Mathlib.AlgebraicGeometry.PullbackCarrier

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Pullback

variable {X Y S : Scheme.{u}}

/-- Prescribed points of two schemes over a common base lift to their scheme pullback exactly
when their images in the base agree. -/
theorem exists_point_iff (f : X ⟶ S) (g : Y ⟶ S) (x : X) (y : Y) :
    (∃ z : (pullback f g : Scheme), pullback.fst f g z = x ∧ pullback.snd f g z = y) ↔
      f x = g y := by
  constructor
  · rintro ⟨z, hzx, hzy⟩
    rw [← hzx, ← hzy]
    exact congr($(pullback.condition (f := f) (g := g)) z)
  · exact exists_preimage_pullback (f := f) (g := g) x y

end AlgebraicGeometry.Scheme.Pullback

namespace AlgebraicGeometry.Scheme

/-- The comparison from the points of a self-pullback of schemes to the pullback of the
underlying maps is surjective. -/
theorem pullbackComparison_forget_self_surjective {X S : Scheme.{u}} (f : X ⟶ S) :
    Function.Surjective (pullbackComparison Scheme.forget f f) := sorry

end AlgebraicGeometry.Scheme
