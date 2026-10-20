module

public import ReasLib.CategoryTheory.Sites.Grothendieck.SheafComparison

@[expose] public section

open CategoryTheory Opposite

universe u v w

#check (CategoryTheory.Grothendieck.toSheafSystem :
  ∀ (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
  [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
  [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
      ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
  [CategoryTheory.Grothendieck.IsFiberwiseSite F J],
    Sheaf (CategoryTheory.Grothendieck.topology F J) (Type w) ⥤
      CategoryTheory.SimplicialSites.SheafSystem (fun n ↦ (J (op n)).toGrothendieck)
      (fun φ ↦ CategoryTheory.Grothendieck.toposMap F J φ))
