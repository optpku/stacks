module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.ClosedImmersion
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.FiniteType

/-!
# Closed immersions are locally of finite type
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.ClosedImmersion

/-- A closed immersion of presheaves over a scheme is locally of finite type. -/
instance locallyOfFiniteType {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) [ClosedImmersion f] : LocallyOfFiniteType f :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace.ClosedImmersion
