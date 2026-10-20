module

public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable.Hom
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u v

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J (Type (max u v))] (F : Sheaf J (Type (max u v))) (U : C)

/- 7.12.3.1: on a site C, for every sheaf of sets F and object U,
Mor_Sh(C)(h_U^#, F) = Mor_PSh(C)(h_U, F) = F(U). The first identification is
sheafification adjointness and the second is Yoneda; no subcanonical hypothesis
is used. This is the composite Equiv
J.sheafifiedRepresentableHomEquiv F U :
(J.sheafifiedRepresentable U ⟶ F) ≃ F.obj.obj (op U). -/
@[stacks 090I] #check (CategoryTheory.GrothendieckTopology.sheafifiedRepresentableHomEquiv J F U :
  (J.sheafifiedRepresentable U ⟶ F) ≃ F.obj.obj (op U))

#check ((sheafificationAdjunction J (Type (max u v))).homEquiv
    (uliftYoneda.{max u v}.obj U) F :
  (J.sheafifiedRepresentable U ⟶ F) ≃ (uliftYoneda.{max u v}.obj U ⟶ F.obj))

#check (uliftYonedaEquiv.{max u v} :
  (uliftYoneda.{max u v}.obj U ⟶ F.obj) ≃ F.obj.obj (op U))
