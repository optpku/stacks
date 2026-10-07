module

public import ReasLib.CategoryTheory.Adjunction.BaseChange

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedBaseChange

/-- The inverse mate of an isomorphism of right-adjoint squares is an isomorphism. -/
theorem mapOfRight_isIso
    {C D C' D' : Type u} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {L' : C' ⥤ D'} {R : D ⥤ C} {R' : D' ⥤ C'}
    {G : C ⥤ C'} {H : D ⥤ D'} (adj : L ⊣ R) (adj' : L' ⊣ R')
    (square : R ⋙ G ⟶ H ⋙ R') [IsIso square] :
    IsIso (mapOfRight adj adj' square) := sorry

end CategoryTheory.DerivedBaseChange

