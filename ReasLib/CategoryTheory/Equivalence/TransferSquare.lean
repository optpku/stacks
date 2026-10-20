module

public import Mathlib.CategoryTheory.Equivalence

@[expose] public section

open CategoryTheory
noncomputable section

namespace CategoryTheory.Equivalence

/-- Transfer a commuting square across specified equivalences, using their unit and counit. -/
def transferSquare.{uA, uB, uC, uD} {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
    [Category A] [Category B] [Category C] [Category D]
    (E : A ≌ B) (F : C ≌ D) (H : B ⥤ D) (K : A ⥤ C)
    (e : K ⋙ F.functor ≅ E.functor ⋙ H) :
    H ⋙ F.inverse ≅ E.inverse ⋙ K :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight E.counitIso.symm (H ⋙ F.inverse) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft E.inverse
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight e.symm F.inverse ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft K F.unitIso.symm ≪≫ Functor.rightUnitor K)

end CategoryTheory.Equivalence

