module

public import ReasLib.RepresentationTheory.Homological.ContCohomology.FiniteDimensional
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 59.57.5 -/
@[stacks 0DVF] #check
  (CategoryTheory.Action.ModuleCat.DiscreteModuleCat.finiteDimensional_h1 :
    ∀ {k G : Type u} [Field k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      (M : CategoryTheory.Action.ModuleCat.DiscreteModuleCat k G)
      [FiniteDimensional k M.obj.V],
      TopologicalGroup.IsFinitelyGenerated G →
      FiniteDimensional k
        (CategoryTheory.Action.ModuleCat.DiscreteModuleCat.cohomologyObject k G 1 M))

end
