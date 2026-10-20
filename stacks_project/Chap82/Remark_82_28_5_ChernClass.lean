module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.RankGluedChern
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.OperationalFirstChern
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ProjSymChart
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ProjectiveBaseChange

/-! Canonical rankwise Chern operations on the actual rational-equivalence quotient.
The implementation is the explicit Proj(Sym) / tautological / Segre construction.
No parallel cycle-as-Chow ring or chosen positive Chern family remains. -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.ChernClass.chernClass :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (E : X.Modules) [SheafOfModules.IsFiniteLocallyFree E] (i : ℕ),
    ChowCohomology.degree δ f (i : ℤ))
