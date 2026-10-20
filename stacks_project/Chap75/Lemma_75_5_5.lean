module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pullback.Preservation
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Lemma_75_26_4_Pullback

@[expose] public section

open AlgebraicGeometry.AlgebraicSpace CategoryTheory ObjectProperty

universe u

/- Lemma 75.5.5: Let `S` be a scheme. Let `f : Y ⟶ X` be a morphism of algebraic
spaces over `S`. The functor `Lf^*` sends `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_Y)`. -/
@[stacks 08F4] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.pullback_preservesQuasiCoherent :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {Y X : AlgebraicGeometry.AlgebraicSpace S}
      (f : Y ⟶ X),
      derivedQuasiCoherentModuleProperty X ≤
        (derivedQuasiCoherentModuleProperty Y).inverseImage (ModuleDerived.pullback f))

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

namespace pullback

/-- Total left derived module pullback preserves quasi-coherent cohomology. -/
theorem mapsTo {S : Scheme.{u}} {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    derivedQuasiCoherentModuleProperty X ≤
      (derivedQuasiCoherentModuleProperty Y).inverseImage (modulePullbackDerived f) := by
  intro K hK n
  exact ObjectProperty.prop_of_iso (quasiCoherentModuleProperty Y)
    ((DerivedCategory.homologyFunctor (Modules Y) n).mapIso
      ((ModuleDerived.pullbackIsoTotalLeftDerived f).app K))
    (ModuleDerived.pullback_preservesQuasiCoherent f K hK n)

end pullback

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
