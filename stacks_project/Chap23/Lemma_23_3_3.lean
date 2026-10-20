module

public import ReasLib.RingTheory.DividedPowers.Category.Corepresentable
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

section

variable (F : DividedPowerRing.{u} ⥤ Type u)
variable [PreservesLimits F]
variable (hF : F.HasBoundedElementSources)

/- Lemma 23.3.3 (tag `07GW`): a limit-preserving functor on divided power rings is
corepresentable when its elements have uniformly bounded sources. -/
@[stacks 07GW]
#check (CategoryTheory.Functor.HasBoundedElementSources.isCorepresentable (F := F) hF :
  F.IsCorepresentable)

end

#check @CategoryTheory.Functor.ElementsBoundedBy
#check @CategoryTheory.Functor.HasBoundedElementSources
