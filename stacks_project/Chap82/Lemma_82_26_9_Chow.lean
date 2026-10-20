module

public import Mathlib.Topology.LocallyFinsupp
public import stacks_project.Chap82.Definition_82_15_1_Chow

/-!
# Fundamental class of an integral good algebraic space

An integral good algebraic space has a fundamental cycle given by the weight-1
generic-point cycle, and a fundamental class `[X]` in `CH_n(X)` obtained by
applying `Hom.chowMk`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Function

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]

/-- The weight-1 cycle supported at the generic point of an integral good space. -/
def fundamentalCycle [IsIntegral X] : Function.locallyFinsupp (Points X) ℤ :=
  let _ := δ
  @Function.locallyFinsuppWithin.single (Points X) _ ℤ (Classical.decEq _) _
    (genericPoint_of_good f (univIrreducibleClosed X)) (1 : ℤ)

/-- The fundamental cycle of an integral good space is a cycle of degree
`dim_δ(X)`. -/
theorem mem_cycleGroup_fundamentalCycle [IsIntegral X] :
    (Hom.fundamentalCycle (f)) δ ∈
      (Hom.cycleGroup (f)) δ ((Hom.deltaDimension (f)) δ (univIrreducibleClosed X)) :=
  sorry

/-- The fundamental cycle is the weight-1 singleton at the generic point. -/
theorem fundamentalCycle_eq [IsIntegral X] :
    (Hom.fundamentalCycle (f)) δ =
      @Function.locallyFinsuppWithin.single (Points X) _ ℤ (Classical.decEq _) _
        (genericPoint_of_good f (univIrreducibleClosed X)) (1 : ℤ) :=
  sorry

/-- The fundamental class `[X]` in `CH_n(X)`, where `n = dim_δ(X)`. -/
def fundamentalClass [IsIntegral X] :
    (Hom.chowGroup (f)) δ ((Hom.deltaDimension (f)) δ (univIrreducibleClosed X)) :=
  (Hom.chowMk (f)) δ ((Hom.deltaDimension (f)) δ (univIrreducibleClosed X))
    ⟨(Hom.fundamentalCycle (f)) δ, mem_cycleGroup_fundamentalCycle f δ⟩

/-- The fundamental class is the Chow class of the weight-1 generic-point cycle. -/
theorem fundamentalClass_eq [IsIntegral X] :
    (Hom.fundamentalClass (f)) δ =
      (Hom.chowMk (f)) δ ((Hom.deltaDimension (f)) δ (univIrreducibleClosed X))
        ⟨(Hom.fundamentalCycle (f)) δ, mem_cycleGroup_fundamentalCycle f δ⟩ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
