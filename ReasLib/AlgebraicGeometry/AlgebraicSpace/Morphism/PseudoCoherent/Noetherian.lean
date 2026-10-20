module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.PseudoCoherent

/-!
# Pseudo-coherent morphisms over locally Noetherian algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PseudoCoherent

/-- A morphism of algebraic spaces to a locally Noetherian algebraic space is pseudo-coherent
if and only if it is locally of finite type. -/
theorem iff_locallyOfFiniteType {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsLocallyNoetherian Y] :
    PseudoCoherent f ↔ LocallyOfFiniteType f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.PseudoCoherent
