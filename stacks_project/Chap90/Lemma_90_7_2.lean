module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Completion
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]

/- Lemma 90.7.2: if `p : F ⥤ ArtinianLocalAlgCat Λ k` is cofibered in groupoids, then
the completion `completion p : FormalObject p ⥤ CompleteLocalAlgCat Λ k` is cofibered
in groupoids, i.e. `IsFibered.InGroupoids (completion p).op`. -/
@[stacks 06H4]
#check (CategoryTheory.Functor.completion_op_isFiberedInGroupoids :
    ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k)
      [CategoryTheory.Functor.IsFibered.InGroupoids p.op],
      CategoryTheory.Functor.IsFibered.InGroupoids
        (CategoryTheory.Functor.completion p).op)
