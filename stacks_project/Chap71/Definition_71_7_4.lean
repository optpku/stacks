module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RegularSection
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

/- Definition 71.7.4
Let `S` be a scheme, `X` an algebraic space over `S`, and `ℒ` an invertible sheaf on `X`.
A global section `s` of `ℒ` is regular if the map `𝒪_X ⟶ ℒ`, sending `f` to `f * s`, is
injective. On the small étale site of `X`, this is the specialization of the generic
module-sheaf predicate `SheafOfModules.IsRegularSection`.
-/
@[stacks 0843] #check (SheafOfModules.IsRegularSection :
  ∀ {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} (ℒ : SheafOfModules.{w} R), ℒ.sections → Prop)
