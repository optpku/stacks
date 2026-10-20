module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.Preservation.Pullback

/-!
# Cancellation of limit-preserving transformations

If a composite transformation of set-valued functors on schemes over a base is
limit preserving and the second factor is limit preserving, then the first
factor is limit preserving.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme.Over.IsLimitPreserving

/-- A limit-preserving transformation can be cancelled on the right when its
composite with a second transformation is limit preserving. -/
theorem of_comp {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type v} {a : F ⟶ G} {b : G ⟶ H}
    (hba : IsLimitPreserving (a ≫ b)) (hb : IsLimitPreserving b) :
    IsLimitPreserving a :=
  sorry

end AlgebraicGeometry.Scheme.Over.IsLimitPreserving
