module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.FilteredK0.FirstChern

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

/- Lemma 42.69.7: for a coherent module whose support has relative dimension at most
`k + 1`, its filtered Grothendieck class change under an invertible tensor twist is the
image of the first Chern class capped with its degree-`k + 1` associated cycle. -/
@[stacks 02SX] #check
  (AlgebraicGeometry.Scheme.Modules.FilteredK0.toFilteredK0_firstChernClassCap :
    ∀ {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
      (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)
      (L : X.Modules) [Scheme.Modules.Invertible L]
      (F : RingedSpace.CohLE X.toRingedSpace (p.relativeDimensionFunction δ) (k + 1)),
      ChowGroup.toFilteredK0 p δ k
          (Scheme.Modules.firstChernClassCap p δ L k
            (Scheme.Modules.GradedK0.objectCycle p δ (k + 1) F)) =
        Scheme.Modules.FilteredK0.tensorDifference p δ k L F)

/- The same tensor-difference class belongs to the image of the degree-`k` graded
Grothendieck group. -/
#check
  (AlgebraicGeometry.Scheme.Modules.FilteredK0.tensorDifference_mem_filteredImage :
    ∀ {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
      (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)
      (L : X.Modules) [Scheme.Modules.Invertible L]
      (F : RingedSpace.CohLE X.toRingedSpace (p.relativeDimensionFunction δ) (k + 1)),
      Scheme.Modules.FilteredK0.tensorDifference p δ k L F ∈
        Scheme.Modules.GradedK0.filteredImage p δ k)
