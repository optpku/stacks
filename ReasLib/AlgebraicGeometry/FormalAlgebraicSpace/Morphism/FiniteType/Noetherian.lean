module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Types
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.FiniteType

/-!
# Local Noetherianity along locally finite type morphisms of formal algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.LocallyOfFiniteType

/-- The source of a locally of finite type morphism of formal algebraic spaces
over a scheme is locally Noetherian if its target is locally Noetherian. -/
theorem isLocallyNoetherian {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsLocallyNoetherian Y] :
    IsLocallyNoetherian X :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace.LocallyOfFiniteType
