module

public import Mathlib.CategoryTheory.Action.Continuous
public import Mathlib.Topology.Category.FinTopCat

@[expose] public section

open CategoryTheory
open scoped FintypeCatDiscrete

noncomputable section
universe u v

namespace CategoryTheory.ContAction

/-- Finite continuous actions already carry the discrete topology. -/
def finiteDiscreteEquivalence (G : Type v) [Monoid G] [TopologicalSpace G] :
    ContAction FintypeCat.{u} G ≌ DiscreteContAction FintypeCat.{u} G where
  functor :=
    { obj := fun X ↦ ⟨X, by change DiscreteTopology X.obj.V; infer_instance⟩
      map := fun f ↦ ObjectProperty.homMk f }
  inverse := forget₂ _ _
  unitIso := NatIso.ofComponents (fun X ↦ Iso.refl X)
  counitIso := NatIso.ofComponents (fun X ↦ ObjectProperty.isoMk _ (Iso.refl X.obj))

end CategoryTheory.ContAction

end
