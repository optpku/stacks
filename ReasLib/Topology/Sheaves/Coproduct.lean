module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Topology.Sheaves.Skyscraper
public import Mathlib.Topology.Sheaves.Stalks
public import ReasLib.CategoryTheory.Sites.Sheaf.Colimit
public import ReasLib.Topology.Sheaves.Abelian

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}}
variable {I : Type u} (F : I → X.Sheaf AddCommGrpCat.{u})

/-- The coproduct of abelian sheaves is the sheafification of the coproduct of their underlying
abelian presheaves. -/
noncomputable def coproductIsoSheafify :
    ∐ F ≅
      (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (∐ fun i ↦ (forget AddCommGrpCat.{u} X).obj (F i)) :=
  let hs : HasColimitsOfShape (Discrete I) (X.Sheaf AddCommGrpCat.{u}) :=
    CategoryTheory.Sheaf.instHasColimitsOfShape
  let hp : HasColimitsOfShape (Discrete I) (X.Presheaf AddCommGrpCat.{u}) :=
    functorCategoryHasColimitsOfShape
  let h1 : HasColimit (Discrete.functor F) :=
    @HasColimitsOfShape.has_colimit _ _ _ _ hs (Discrete.functor F)
  let h2 : HasColimit (Discrete.functor F ⋙
      sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    @HasColimitsOfShape.has_colimit _ _ _ _ hp _
  (@CategoryTheory.Sheaf.sheafifyColimitIso _ _ _ _ _ _ _
    (inferInstance) (Discrete.functor F) h1 h2).symm ≪≫
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapIso
      (HasColimit.isoOfNatIso (Discrete.compNatIsoDiscrete F (forget AddCommGrpCat.{u} X)))

/-- The stalk of a coproduct of abelian sheaves is the coproduct of the stalks. -/
noncomputable def stalkCoproductIso (x : X) :
    (∐ F).presheaf.stalk x ≅ ∐ fun i ↦ (F i).presheaf.stalk x :=
  PreservesCoproduct.iso
    (forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) F

/-- The stalk coproduct comparison carries each coproduct inclusion to the corresponding stalk
coproduct inclusion. -/
theorem stalkCoproductIso_ι (x : X) (i : I) :
    (forget AddCommGrpCat.{u} X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (Sigma.ι F i) ≫
      (stalkCoproductIso F x).hom =
    Sigma.ι (fun j ↦ (F j).presheaf.stalk x) i := sorry

end TopCat.Sheaf

end

end
