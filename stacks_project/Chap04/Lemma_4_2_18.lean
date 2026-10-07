module

public import ReasLib.CategoryTheory.Functor.ObjwiseIsoLift
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable (F : A ⥤ B)

/- Lemma 4.2.18 (1): a fully faithful functor with prescribed preimage objects and objectwise
isomorphisms has a unique functorial lift with those objects. -/
@[stacks 05SG "unique functor extending the chosen object assignment"]
#check (Functor.objwiseIsoLift.existsUnique F :
  ∀ [F.Full] [F.Faithful] (jObj : B → A) (i : ∀ X : B, X ≅ F.obj (jObj X)),
    ∃! j : B ⥤ A,
      ∃ hjObj : ∀ X : B, j.obj X = jObj X,
        ∃ α : 𝟭 B ≅ j ⋙ F,
          ∀ X : B,
            α.hom.app X =
              (i X).hom ≫
                eqToHom (congrArg (fun Z ↦ F.obj Z) (hjObj X).symm))

/- Lemma 4.2.18 (2): the prescribed lift and the original functor form an explicit equivalence. -/
section

variable [F.Full] [F.Faithful]
variable (jObj : B → A) (i : ∀ X : B, X ≅ F.obj (jObj X))

@[stacks 05SG "chosen lift and original functor are quasi-inverse"]
#check (Functor.objwiseIsoLift.equivalence F jObj i : A ≌ B)

end

end CategoryTheory.Functor
