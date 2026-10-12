/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Locus.Noetherian

/-!
# Flat loci of morphisms over locally Noetherian schemes
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The flat locus of a locally finite type morphism to a locally Noetherian
scheme is open. -/
theorem isOpen_flatAt_of_locallyNoetherian
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian Y]
    [LocallyOfFiniteType f] :
    IsOpen {x : X | flatAt f x} := sorry

end AlgebraicGeometry.Scheme.Hom
