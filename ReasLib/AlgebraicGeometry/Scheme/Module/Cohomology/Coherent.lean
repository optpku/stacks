module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Characterization
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.Perfect.Tensor

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- If `R` is coherent, `X` is of finite presentation over `R`, and `G` is finitely presented
and flat over `R` with proper support over `R`, then every cohomology module `H^i(X, G)` is a
coherent `R`-module. -/
@[instance]
theorem cohomologyCoherent
    {R : Type u} [CommRing R] [IsCoherentRing R] {X : Scheme.{u}}
    [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (f : X ⟶ Spec (CommRingCat.of R)) [Scheme.Hom.FinitePresentation f]
    (G : X.Modules) [G.IsFinitePresentation] [SheafOfModules.IsFlatOver G f.toShHom]
    [Scheme.Modules.HasProperSupportOver f G] (i : ℕ) :
    Module.Coherent R (cohomology f G i) := sorry

end AlgebraicGeometry.Scheme.Hom
