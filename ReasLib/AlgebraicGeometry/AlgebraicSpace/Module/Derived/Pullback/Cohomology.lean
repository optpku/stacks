module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Single
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Cohomology.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Unbounded.LeftDerived.Bounds

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Modules
open DerivedCategory.TStructure Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- The unbounded comparison `f^* H^i(E) ⟶ H^i(Lf^* E)`. It is ordinary pullback of
`TruncGE.homologyIso.inv`, the lower-edge comparison on `τ_{≥ i} E`, and the inverse
left-derived lower-truncation homology identification. -/
def cohomologySheafPullbackComparison {Y X : AlgebraicSpace S} (f : Y ⟶ X)
    (E : ModuleDerived X) (i : ℤ) :
    (Modules.pullback f).obj (cohomologySheaf E i) ⟶
      cohomologySheaf ((pullback f).obj E) i :=
  (Modules.pullback f).map (DerivedCategory.TruncGE.homologyIso E i i le_rfl).inv ≫
    cohomologyPullbackComparison f ((t.truncGE i).obj E) i inferInstance inferInstance ≫
      (Functor.LeftDerived.Homotopy.TruncGE.homologyIso
        (Modules.pullback f) (pullback f)
        (ModuleDerived.pullbackCounit f)
        E i i le_rfl).inv

/-- `cohomologySheafPullbackComparison` is ordinary pullback of `TruncGE.homologyIso.inv`,
the lower-edge comparison on `τ_{≥ i} E`, and the inverse left-derived lower-truncation
homology identification. -/
theorem cohomologySheafPullbackComparison_eq {Y X : AlgebraicSpace S} (f : Y ⟶ X)
    (E : ModuleDerived X) (i : ℤ) :
    cohomologySheafPullbackComparison f E i =
      (Modules.pullback f).map (DerivedCategory.TruncGE.homologyIso E i i le_rfl).inv ≫
        cohomologyPullbackComparison f ((t.truncGE i).obj E) i inferInstance inferInstance ≫
          (Functor.LeftDerived.Homotopy.TruncGE.homologyIso
            (Modules.pullback f) (pullback f)
            (ModuleDerived.pullbackCounit f)
            E i i le_rfl).inv :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
