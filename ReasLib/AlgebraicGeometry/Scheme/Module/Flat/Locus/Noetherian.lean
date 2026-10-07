module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Locus

/-!
# Flat loci over locally Noetherian schemes
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The locus where a coherent module is flat over a locally Noetherian target
is open for a locally finite type morphism. -/
theorem isOpen_flatOverAt_of_locallyNoetherian
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian Y]
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsCoherent] :
    IsOpen {x : X | flatOverAt F f x} := sorry

end AlgebraicGeometry.Scheme.Modules
