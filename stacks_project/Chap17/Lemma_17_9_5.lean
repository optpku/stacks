module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteType.Neighborhood
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Stalk
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 17.9.5 (01B9): a finite-type module sheaf with zero stalk vanishes on some open
neighborhood. -/
@[stacks 01B9]
#check fun {X : RingedSpace.{u}} (F : X.Modules) (x : X) [F.IsFiniteType]
    (hFx : IsZero (RingedSpace.stalkModuleCat F x)) ↦
  SheafOfModules.IsFiniteType.existsNeighborhood_isZeroOfCommRing
    (𝒪 := X.sheaf) F x hFx
