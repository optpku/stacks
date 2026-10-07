module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.ChernCharacter
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Dual

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChernClass.Theory

/-- The degree-`i` Chern-character component of the dual of a finite locally free
module `E` is `(-1) ^ i` times the corresponding component of `E`. -/
theorem characterComponent_dual
    {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    (classes : Theory δ p) (E : X.Modules) [E.IsFiniteLocallyFree] (i : ℕ) :
    characterComponent δ p classes (Scheme.Modules.dual E) i =
      ((-1 : ℤ) ^ i) • characterComponent δ p classes E i := sorry

end AlgebraicGeometry.ChernClass.Theory
