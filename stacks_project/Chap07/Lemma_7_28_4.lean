module

public import ReasLib.CategoryTheory.Sites.Over.Cocontinuity
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.28.4

The cocontinuity of the slice functor is already part of Mathlib's slice-site
API.  ReasLib owns the resulting direct-image comparison, so this Chapter 7
entry remains a source-facing recall block.
-/

@[expose] public section

universe uC vC uD vD

namespace CategoryTheory

section

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable (u : C ⥤ D) (U : C)
variable [u.IsCocontinuous J K]

/- Lemma 7.28.4 (03EG): if `u : C ⥤ D` is cocontinuous, then the induced
functor `Over.post u : C / U ⥤ D / u.obj U` is cocontinuous.  The resulting
square of cocontinuous sheaf direct images is the reusable ReasLib comparison
`Functor.sheafPushforwardCocontinuousOverPostComp`. -/
@[stacks 03EG] #check
  (inferInstance :
    (Over.post u).IsCocontinuous (J.over U) (K.over (u.obj U)))

@[stacks 03EG] #check @Functor.sheafPushforwardCocontinuousOverPostComp

end

end CategoryTheory
