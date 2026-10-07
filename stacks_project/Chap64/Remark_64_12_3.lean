module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Characterization
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

/- Remark 64.12.3. On a Noetherian scheme `X`, the category `D_perf(𝒪_X)` is
`RingedSpace.ModuleDerived.Perfect`, the full subcategory of complexes locally
quasi-isomorphic to a finite complex of finite locally free `𝒪_X`-modules
(`LocalModel.finiteLocallyFree`, equivalently `IsPerfect` by
`LocalModel.isPerfect_iff_finiteLocallyFree`). An object `K` of `D(𝒪_X)` is
perfect if and only if it has coherent cohomology sheaves and finite Tor
dimension. -/
@[stacks 03TP] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.isPerfect_iff_coherentCohomology_and_hasFiniteTorDimension :
    ∀ {X : Scheme.{u}} [IsNoetherian X]
      (K : RingedSpace.ModuleDerived X.toRingedSpace),
      RingedSpace.ModuleDerived.IsPerfect K ↔
        DerivedCategory.cohomologyIn
          (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) K ∧
          RingedSpace.HasFiniteTorDimension K)

end AlgebraicGeometry.Scheme.ModuleDerived
