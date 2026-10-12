/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Sheafification.FreeAbelianRepresentable
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)

section

variable [HasWeakSheafify J (Type (max u v))]
variable (U : C) (F : Sheaf J (Type (max u v)))

/- Lemma 18.5.2 (03AB) (1): maps from a sheafified representable are sections. -/
@[stacks 03AB "sheafified representable"]
#check (J.sheafifiedRepresentableHomEquiv F U :
  (J.sheafifiedRepresentable U ⟶ F) ≃ F.obj.obj (op U))

end

section

variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.HasSheafCompose (forget AddCommGrpCat.{max u v})]
variable (G : Sheaf J (Type (max u v)))
variable (A : Sheaf J AddCommGrpCat.{max u v})

/- Lemma 18.5.2 (03AB) (2): the free-forgetful adjunction on sheaves. -/
@[stacks 03AB "free-forgetful adjunction"]
#check ((Sheaf.adjunction J AddCommGrpCat.adj).homEquiv G A :
  ((Sheaf.composeAndSheafify J AddCommGrpCat.free).obj G ⟶ A) ≃
    (G ⟶ (sheafForget J).obj A))

end

section

variable [HasWeakSheafify J (Type (max u v))]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.HasSheafCompose (forget AddCommGrpCat.{max u v})]
variable (U : C) (A : Sheaf J AddCommGrpCat.{max u v})

/- Lemma 18.5.2 (03AB) (3): maps from a free abelian sheafified representable are sections. -/
@[stacks 03AB "free abelian representable"]
#check (FreeAbelianRepresentable.homEquiv J U A :
  (FreeAbelianRepresentable.obj J U ⟶ A) ≃ A.obj.obj (op U))

end

end CategoryTheory
