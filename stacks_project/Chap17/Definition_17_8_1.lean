module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.LocalGeneration.Neighborhood
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry TopologicalSpace

universe u

/- The arbitrary-site owner for local generation by sections is the canonical property
`SheafOfModules.IsLocallyGeneratedBySections`. -/
#check fun {X : RingedSpace.{u}} (F : X.Modules) ↦
  (SheafOfModules.IsLocallyGeneratedBySections F : Prop)

/- Definition 17.8.1 (01B2): on an opens site, the canonical cover-based property is equivalent
to the source's pointwise open-neighborhood formulation. -/
@[stacks 01B2]
#check fun {X : RingedSpace.{u}} (F : X.Modules) ↦
  (SheafOfModules.IsLocallyGeneratedBySections.iffExistsNeighborhood F :
    SheafOfModules.IsLocallyGeneratedBySections F ↔
      ∀ x : X, ∃ U : Opens X,
        x ∈ U ∧ SheafOfModules.IsGloballyGenerated (F.over U))
