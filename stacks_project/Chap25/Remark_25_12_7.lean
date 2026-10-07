module

public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Singleton
import StacksCheckRecall

@[expose] public section

universe w v u

namespace CategoryTheory.Limits.FormalCoproduct

variable {C : Type u} [Category.{v} C]
variable {K L : FormalCoproduct.{w} C}
variable [HasCoproduct K.obj] [HasCoproduct L.obj]

/- Remark 25.12.7: a morphism of formal coproduct families induces the canonical map between
their realized coproduct objects. -/
@[stacks 0DB0]
#check (FormalCoproduct.coproductMap :
  (K ⟶ L) → ((∐ K.obj) ⟶ ∐ L.obj))

/- Coproduct inclusions recover the component maps. -/
#check @FormalCoproduct.ι_coproductMap

/- The construction respects identities and composition. -/
#check @FormalCoproduct.coproductMap_id
#check @FormalCoproduct.coproductMap_comp

end CategoryTheory.Limits.FormalCoproduct
