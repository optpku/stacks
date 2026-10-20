module

import ReasLib.Topology.NonSpectralCounterexample
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite Set TopCat TopologicalSpace

noncomputable section

universe u

/- Example 59.82.5 (1): the distinguished subset is closed. -/
@[stacks 0CAF] #check
  (Topology.NonSpectralCounterexample.counterexampleClosedSubset_isClosed :
    ∀ {Y : Type u} [TopologicalSpace Y] [T1Space Y] (y : Y),
      ¬ IsOpen ({y} : Set Y) →
        @IsClosed (Y ⊕ Unit)
          (Topology.NonSpectralCounterexample.counterexampleTopology y)
          (Topology.NonSpectralCounterexample.counterexampleClosedSubset y))

/- Example 59.82.5 (2): every closure intersection with the distinguished subset is connected. -/
@[stacks 0CAF] #check
  (Topology.NonSpectralCounterexample.counterexampleClosedSubset_closure_inter_isConnected :
    ∀ {Y : Type u} [TopologicalSpace Y] [T1Space Y] (y : Y),
      ¬ IsOpen ({y} : Set Y) → ∀ z : Y ⊕ Unit,
        @IsConnected (Y ⊕ Unit)
          (Topology.NonSpectralCounterexample.counterexampleTopology y)
          (Topology.NonSpectralCounterexample.counterexampleClosedSubset y ∩
            @closure (Y ⊕ Unit)
              (Topology.NonSpectralCounterexample.counterexampleTopology y)
              ({z} : Set (Y ⊕ Unit))))

/- Example 59.82.5 (3): the ambient counterexample space is connected. -/
@[stacks 0CAF] #check
  (Topology.NonSpectralCounterexample.counterexampleSpace_isConnected :
    ∀ {Y : Type u} [TopologicalSpace Y] [T1Space Y] (y : Y),
      ¬ IsOpen ({y} : Set Y) →
        @IsConnected (Y ⊕ Unit)
          (Topology.NonSpectralCounterexample.counterexampleTopology y) Set.univ)

/- Example 59.82.5 (4): the distinguished closed subset is not connected. -/
@[stacks 0CAF] #check
  (Topology.NonSpectralCounterexample.counterexampleClosedSubset_not_isConnected :
    ∀ {Y : Type u} [TopologicalSpace Y] [T1Space Y] (y : Y),
      ¬ IsOpen ({y} : Set Y) →
        ¬ @IsConnected (Y ⊕ Unit)
          (Topology.NonSpectralCounterexample.counterexampleTopology y)
          (Topology.NonSpectralCounterexample.counterexampleClosedSubset y))

/- Example 59.82.5 (5): the constant two-valued sheaf restriction map is not bijective. -/
@[stacks 0CAF] #check
  (Topology.NonSpectralCounterexample.counterexampleConstantSheaf_restriction_not_bijective :
    ∀ {Y : Type u} [TopologicalSpace Y] [T1Space Y] (y : Y),
      ¬ IsOpen ({y} : Set Y) →
        ¬ Function.Bijective
          (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
            (TopCat.subsetInclusion
              (Topology.NonSpectralCounterexample.counterexampleClosedSubset y))).unit.app
            (Topology.NonSpectralCounterexample.counterexampleConstantSheaf y)).hom.app
              (op (⊤ : Opens
                (Topology.NonSpectralCounterexample.counterexampleSpace y)))))

end

end
