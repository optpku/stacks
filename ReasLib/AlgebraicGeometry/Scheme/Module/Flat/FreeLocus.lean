module
public import ReasLib.AlgebraicGeometry.Scheme.Module.FreeLocus
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Locus.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.FiberCriterion.FreeNeighborhood
@[expose] public section
open CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
namespace AlgebraicGeometry.Scheme.Modules
/-- The free locus is open for a finitely presented module flat over a locally finitely presented morphism. -/
theorem isOpen_freeLocus_of_flatOver {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsFinitePresentation] (h_flat : flatOver F f) :
    IsOpen (freeLocus F : Set X) := sorry
/-- The free locus commutes with arbitrary base change under relative flatness. -/
theorem freeLocus_baseChange {X S S' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsFinitePresentation] (h_flat : flatOver F f) (g : S' ⟶ S) :
    freeLocus (baseChangeModule f g F) = (Opens.map (pullback.fst f g).base).obj (freeLocus F) := sorry
end AlgebraicGeometry.Scheme.Modules
