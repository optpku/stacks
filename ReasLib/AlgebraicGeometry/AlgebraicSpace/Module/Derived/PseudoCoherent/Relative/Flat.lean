module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation.FiniteType

/-! # Relative pseudo-coherence over flat morphisms -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/-- For a flat, locally finitely presented morphism of algebraic spaces, a derived
module with quasi-coherent cohomology is relatively pseudo-coherent if and only
if it is pseudo-coherent on the source. -/
theorem isPseudoCoherentOver_iff_isPseudoCoherent {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicGeometry.AlgebraicSpace.Flat f]
    [AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation f]
    {E : ModuleDerived X} (hE : derivedQuasiCoherentModuleProperty X E) :
    IsPseudoCoherentOver f E ↔ AlgebraicGeometry.AlgebraicSpace.IsPseudoCoherent X E := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
