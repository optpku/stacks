module

public import Mathlib.CategoryTheory.Adjunction.Limits
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

open Limits

universe vJ uJ vC uC vD uD

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

/- The source needs preservation for a chosen adjunction `u ⊣ v`. The canonical owners
`Adjunction.leftAdjoint_preservesColimits` and `Adjunction.rightAdjoint_preservesLimits` state
exactly that for every diagram shape and every pair of object/morphism universes. Their
`functorialityAdjunction` variants are proof machinery, while the `IsLeftAdjoint` and
`IsRightAdjoint` instances forget the chosen adjunction. The preservation classes intentionally
need no ambient `HasColimit` or `HasLimit` assumption: specializing them to a source universal
cocone or cone produces the mapped universal object. Thus neither a pointwise equality nor a
pointwise isomorphism wrapper would add downstream information. -/

/- Lemma 4.24.5 (1): if `u ⊣ v`, then `u` preserves every representable colimit. -/
@[stacks 0038 "left adjoints preserve representable colimits"]
#check (Adjunction.leftAdjoint_preservesColimits adj :
  PreservesColimitsOfSize.{vJ, uJ} L)

/- Lemma 4.24.5 (2): if `u ⊣ v`, then `v` preserves every representable limit. -/
@[stacks 0038 "right adjoints preserve representable limits"]
#check (Adjunction.rightAdjoint_preservesLimits adj :
  PreservesLimitsOfSize.{vJ, uJ} R)

end CategoryTheory
