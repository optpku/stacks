module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u v

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (𝒪 : Sheaf J RingCat.{max u v})
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/- Lemma 18.14.2 (03DB) (1): all small limits exist for 𝒪-module sheaves. -/
@[stacks 03DB "(1)"]
#check (inferInstance : HasLimits (SheafOfModules.{max u v} 𝒪))

/- Lemma 18.14.2 (03DB) (2): all small colimits exist for 𝒪-module sheaves. -/
@[stacks 03DB "(2)"]
#check (inferInstance : HasColimits (SheafOfModules.{max u v} 𝒪))

/- Lemma 18.14.2 (03DB) (3): the underlying-additive-sheaf functor preserves all limits. -/
@[stacks 03DB "(3)"]
#check (SheafOfModules.toSheaf_preservesLimits 𝒪 :
  PreservesLimits (SheafOfModules.toSheaf.{max u v} 𝒪))

/- Lemma 18.14.2 (03DB) (4): it also preserves all colimits. -/
@[stacks 03DB "(4)"]
#check (SheafOfModules.toSheaf_preservesColimits 𝒪 :
  PreservesColimits (SheafOfModules.toSheaf.{max u v} 𝒪))

/- Lemma 18.14.2 (03DB) (5): filtered colimits of 𝒪-module sheaves are exact. -/
@[stacks 03DB "(5)"]
#check @SheafOfModules.hasAB5
