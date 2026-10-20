module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints.Proper

/-!
# Proper functors of points over an algebraic space

A functor on `(Sch/B)ᵒᵖ` is proper over `B` when it is represented by a proper
morphism of algebraic spaces over `B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/- Proper representability of a relative functor of points. -/
#check (AlgebraicGeometry.AlgebraicSpace.IsProperOver :
  ((SchemeOver B)ᵒᵖ ⥤ Type (u + 1)) → Prop)

/- Proper representability is specified by a proper representing morphism. -/
#check (AlgebraicGeometry.AlgebraicSpace.isProperOver_iff :
  ∀ (F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)), IsProperOver F ↔
      ∃ (X : AlgebraicSpace S) (π : X ⟶ B),
        Proper π ∧ Nonempty (F ≅ yonedaOver π))

/- A proper representing morphism exhibits proper representability. -/
#check (AlgebraicGeometry.AlgebraicSpace.IsProperOver.of :
  ∀ {X : AlgebraicSpace S} {π : X ⟶ B} (hProper : Proper π)
    {F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)} (e : F ≅ yonedaOver π), IsProperOver F)

end AlgebraicGeometry.AlgebraicSpace
