module

public import ReasLib.CategoryTheory.Sites.Simplicial.SheafComparison

@[expose] public section

open CategoryTheory Opposite

universe u v w

#check (CategoryTheory.SimplicialSites.toSheafSystem :
  ∀ (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
  [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
  [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
      ((C.map φ).toFunctor).op.HasLeftKanExtension P]
  [CategoryTheory.SimplicialSites.IsMorphismDiagram C J],
    Sheaf (CategoryTheory.SimplicialSites.topology C J) (Type w) ⥤
      CategoryTheory.SimplicialSites.SheafSystem (fun n ↦ (J n).toGrothendieck)
      (fun φ ↦ CategoryTheory.SimplicialSites.toposMap C J φ))
