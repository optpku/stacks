module

public import ReasLib.CategoryTheory.Sites.EnoughObjects
public import ReasLib.CategoryTheory.Sites.WeaklyContractible
import Mathlib.Tactic.CrossRefAttribute

/-!
# Enough weakly contractible objects

Coverings by weakly contractible objects characterize the enough-objects predicates for
chosen coverages and for Grothendieck topologies.
-/

@[expose] public section

universe u v

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

namespace HasEnoughObjectsWithProperty

/-- A Grothendieck topology has enough weakly contractible objects exactly when
every object admits a covering family whose members are weakly contractible. -/
@[stacks 090L "(2)"]
theorem iff_existsWeaklyContractibleCover :
    J.HasEnoughObjectsWithProperty J.IsWeaklyContractible ↔
      ∀ U : C, ∃ families : Limits.FormalCoproduct.{max u v} (CategoryTheory.Over U),
        Sieve.ofArrows (fun i => (families.obj i).left) (fun i => (families.obj i).hom) ∈ J U ∧
          ∀ i : families.index, J.IsWeaklyContractible (families.obj i).left := sorry

end HasEnoughObjectsWithProperty

end CategoryTheory.GrothendieckTopology

namespace CategoryTheory.Coverage

variable {C : Type u} [Category.{v} C] (K : Coverage C)

namespace HasEnoughObjectsWithProperty

/-- A coverage has enough objects weakly contractible for its generated topology exactly when
every object admits a chosen covering family all of whose members are weakly contractible. -/
theorem iff_existsWeaklyContractibleCover :
    K.HasEnoughObjectsWithProperty K.toGrothendieck.IsWeaklyContractible ↔
      ∀ U : C, ∃ families : Limits.FormalCoproduct.{max u v} (CategoryTheory.Over U),
        Presieve.ofArrows (fun i => (families.obj i).left) (fun i => (families.obj i).hom) ∈ K U ∧
          ∀ i : families.index, K.toGrothendieck.IsWeaklyContractible (families.obj i).left := sorry

end HasEnoughObjectsWithProperty

end CategoryTheory.Coverage
