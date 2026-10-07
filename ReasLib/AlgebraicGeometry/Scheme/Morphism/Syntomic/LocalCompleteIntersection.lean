module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Flat
public import ReasLib.RingTheory.RingHom.Syntomic.LocalCompleteIntersection

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Syntomic

/-- A scheme morphism is syntomic if and only if it is flat and locally of
complete-intersection type. -/
@[stacks 069K]
theorem iff_flat_and_isLocalCompleteIntersection {X S : Scheme.{u}} (f : X ⟶ S) :
    Syntomic f ↔ Flat f ∧ LocallyOfType RingHom.IsLocalCompleteIntersection f := sorry

end AlgebraicGeometry.Syntomic
