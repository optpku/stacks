module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Versal
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 90.8.9: let F be a category cofibered in groupoids. Let ξ be a
formal object of F lying over R in Ob(Ĉ_Λ). We say ξ is versal if the
corresponding morphism underline ξ : underline R |_{C_Λ} ⟶ F of Remark 90.7.12
is smooth. This is owned by FormalObject.IsVersal. -/
@[stacks 06HR] #check (FormalObject.IsVersal :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] {F : Type (u + 1)}
    [CategoryTheory.Category.{u + 1, u + 1} F]
    {p : CategoryTheory.Functor F (ArtinianLocalAlgCat Λ k)} (ξ : FormalObject p)
    [CategoryTheory.Functor.IsFibered.InGroupoids p.op], Prop)

#check FormalObject.IsVersal.spec
