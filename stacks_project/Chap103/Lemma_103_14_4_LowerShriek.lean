module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.LowerShriek
public import stacks_project.Chap103.Lemma_103_14_2_Ringed
public import stacks_project.Chap103.Lemma_103_14_2_Topos

/-!
# Module lower shriek along lisse-étale and flat-fppf inclusions

Restriction of modules along the lisse-étale and flat-fppf inclusions of an
algebraic stack admits a left adjoint, the specialization of the continuous and
cocontinuous module lower shriek. The forgetful mate compares this adjoint with
abelian lower shriek, and the unit encodes `g^* g_! = id`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open RingedSite.Cocontinuous

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- Restriction of étale modules to the lisse-étale site, i.e. module inverse
image along the lisse-étale inclusion. -/
abbrev lisseEtaleModuleInverseImage (X : GroupoidsOver S) [AlgebraicStack X] :
    SheafOfModules.{u} (etaleStructureSheaf X) ⥤
      SheafOfModules.{u} (lisseEtaleStructureSheaf X) :=
  moduleInverseImage (lisseEtaleInclusion X) (etaleStructureSheaf X)

/-- Module lower shriek from the lisse-étale site to the associated étale site. -/
abbrev lisseEtaleModuleLowerShriek (X : GroupoidsOver S) [AlgebraicStack X] :
    SheafOfModules.{u} (lisseEtaleStructureSheaf X) ⥤
      SheafOfModules.{u} (etaleStructureSheaf X) :=
  moduleLowerShriek (lisseEtaleInclusion X) (etaleStructureSheaf X)

namespace lisseEtaleModuleLowerShriek

/-- Module lower shriek is left adjoint to lisse-étale module inverse image. -/
def adjunction (X : GroupoidsOver S) [AlgebraicStack X] :
    lisseEtaleModuleLowerShriek X ⊣ lisseEtaleModuleInverseImage X :=
  moduleLowerShriek.adjunction (lisseEtaleInclusion X) (etaleStructureSheaf X)

/-- Hom-sets out of lisse-étale module lower shriek are morphisms into restriction. -/
def homEquiv (X : GroupoidsOver S) [AlgebraicStack X]
    (F : SheafOfModules.{u} (lisseEtaleStructureSheaf X))
    (G : SheafOfModules.{u} (etaleStructureSheaf X)) :
    ((lisseEtaleModuleLowerShriek X).obj F ⟶ G) ≃
      (F ⟶ (lisseEtaleModuleInverseImage X).obj G) :=
  (adjunction X).homEquiv F G

/-- Canonical mate from abelian lower shriek after forgetting module structure to
forgetting after module lower shriek, along the lisse-étale inclusion. -/
def underlyingComparison (X : GroupoidsOver S) [AlgebraicStack X] :
    SheafOfModules.toSheaf.{u} (lisseEtaleStructureSheaf X) ⋙
        lisseEtaleAbelianLowerShriek X ⟶
      lisseEtaleModuleLowerShriek X ⋙
        SheafOfModules.toSheaf.{u} (etaleStructureSheaf X) :=
  moduleLowerShriek.underlyingComparison.{u, u, u + 1, u + 1, u, u}
    (lisseEtaleInclusion X) (etaleStructureSheaf X)

/-- Lisse-étale module lower shriek agrees with abelian lower shriek. -/
instance underlyingComparison_isIso (X : GroupoidsOver S) [AlgebraicStack X] :
    IsIso (underlyingComparison X) :=
  sorry

end lisseEtaleModuleLowerShriek

/-- The unit `id ⟶ g^* g_!` is an isomorphism on lisse-étale modules. -/
theorem lisseEtaleModuleLowerShriek_unit_app_isIso (X : GroupoidsOver S)
    [AlgebraicStack X] (F : SheafOfModules.{u} (lisseEtaleStructureSheaf X)) :
    IsIso ((lisseEtaleModuleLowerShriek.adjunction X).unit.app F) :=
  sorry

/-- Restriction of fppf modules to the flat-fppf site, i.e. module inverse image
along the flat-fppf inclusion. -/
abbrev flatFppfModuleInverseImage (X : GroupoidsOver S) [AlgebraicStack X] :
    SheafOfModules.{u} (structureSheaf X) ⥤
      SheafOfModules.{u} (flatFppfStructureSheaf X) :=
  moduleInverseImage (flatFppfInclusion X) (structureSheaf X)

/-- Module lower shriek from the flat-fppf site to the inherited fppf site. -/
abbrev flatFppfModuleLowerShriek (X : GroupoidsOver S) [AlgebraicStack X] :
    SheafOfModules.{u} (flatFppfStructureSheaf X) ⥤
      SheafOfModules.{u} (structureSheaf X) :=
  moduleLowerShriek (flatFppfInclusion X) (structureSheaf X)

namespace flatFppfModuleLowerShriek

/-- Module lower shriek is left adjoint to flat-fppf module inverse image. -/
def adjunction (X : GroupoidsOver S) [AlgebraicStack X] :
    flatFppfModuleLowerShriek X ⊣ flatFppfModuleInverseImage X :=
  moduleLowerShriek.adjunction (flatFppfInclusion X) (structureSheaf X)

/-- Hom-sets out of flat-fppf module lower shriek are morphisms into restriction. -/
def homEquiv (X : GroupoidsOver S) [AlgebraicStack X]
    (F : SheafOfModules.{u} (flatFppfStructureSheaf X))
    (G : SheafOfModules.{u} (structureSheaf X)) :
    ((flatFppfModuleLowerShriek X).obj F ⟶ G) ≃
      (F ⟶ (flatFppfModuleInverseImage X).obj G) :=
  (adjunction X).homEquiv F G

/-- Canonical mate from abelian lower shriek after forgetting module structure to
forgetting after module lower shriek, along the flat-fppf inclusion. -/
def underlyingComparison (X : GroupoidsOver S) [AlgebraicStack X] :
    SheafOfModules.toSheaf.{u} (flatFppfStructureSheaf X) ⋙
        flatFppfAbelianLowerShriek X ⟶
      flatFppfModuleLowerShriek X ⋙
        SheafOfModules.toSheaf.{u} (structureSheaf X) :=
  moduleLowerShriek.underlyingComparison.{u, u, u + 1, u + 1, u, u}
    (flatFppfInclusion X) (structureSheaf X)

/-- Flat-fppf module lower shriek agrees with abelian lower shriek. -/
instance underlyingComparison_isIso (X : GroupoidsOver S) [AlgebraicStack X] :
    IsIso (underlyingComparison X) :=
  sorry

end flatFppfModuleLowerShriek

/-- The unit `id ⟶ g^* g_!` is an isomorphism on flat-fppf modules. -/
theorem flatFppfModuleLowerShriek_unit_app_isIso (X : GroupoidsOver S)
    [AlgebraicStack X] (F : SheafOfModules.{u} (flatFppfStructureSheaf X)) :
    IsIso ((flatFppfModuleLowerShriek.adjunction X).unit.app F) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
