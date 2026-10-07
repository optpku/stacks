module

public import ReasLib.CategoryTheory.Sites.EnoughObjects
public import ReasLib.CategoryTheory.Sites.WeaklyContractible
import Mathlib.Tactic.CrossRefAttribute

/-!
# Enough weakly contractible objects

The source-facing covering condition is expressed through the general neutral owner
`HasEnoughObjectsWithProperty`.
-/

@[expose] public section

universe u v

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

namespace HasEnoughObjectsWithProperty

/-- Definition 7.40.2 (090L) (2): a site has enough weakly contractible objects exactly when
every object admits a covering family whose members are weakly contractible. -/
@[stacks 090L "(2)"]
theorem iff_existsWeaklyContractibleCover :
    J.HasEnoughObjectsWithProperty J.IsWeaklyContractible ↔
      ∀ U : C, ∃ U' : SemiRepresentableFamily.Over.{max u v} U,
        U'.toSieve ∈ J U ∧
          ∀ i : U'.index, J.IsWeaklyContractible (U'.obj i).left := sorry

end HasEnoughObjectsWithProperty

end CategoryTheory.GrothendieckTopology
