module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Theory
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Dual

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ChernClass.Theory

/-- The degree-`i` Chern class of the dual of a finite locally free module `E` is
`(-1) ^ i` times the degree-`i` Chern class of `E`. -/
theorem component_dual
    {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    (classes : Theory δ p) (E : X.Modules) [E.IsFiniteLocallyFree] (i : ℕ) :
    classes.component (Scheme.Modules.dual E) i =
      ((-1 : ℤ) ^ i) • classes.component E i := sorry

end AlgebraicGeometry.ChernClass.Theory
