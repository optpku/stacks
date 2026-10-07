module

public import stacks_project.Chap90.Definition_90_7_3
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]
variable (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op]

/- Lemma 90.7.2: if `p : F ⥤ ArtinianLocalAlgCat Λ k` is cofibered in groupoids, then
the completion `completion p : FormalObject p ⥤ CompleteLocalAlgCat Λ k` is cofibered
in groupoids, i.e. `IsFibered.InGroupoids (completion p).op`. -/
@[stacks 06H4]
#check (Functor.completion_op_isFiberedInGroupoids p :
    Functor.IsFibered.InGroupoids (Functor.completion p).op)
