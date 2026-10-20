module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.GlobalSections
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Canonical

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor.RightDerived.Bounded

noncomputable section

universe w u

namespace AlgebraicGeometry.Scheme.Etale.BoundedBelow

variable (X : Scheme.{u})
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasDerivedCategory.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [((siteAbelianSectionsFunctor X.smallEtaleTopology (globalEtale X)).mapHomotopyCategoryPlus ⋙
    DerivedCategory.Plus.Qh).HasRightDerivedFunctor
  (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]

/-- Degree-`p` étale hypercohomology on bounded-below complexes of abelian sheaves is
the homology of the bounded-below right derived global sections functor. -/
def hypercohomologyFunctor (p : ℤ) :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u} :=
  functor (siteAbelianSectionsFunctor X.smallEtaleTopology (globalEtale X)) ⋙
    DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} p

/-- The hypercohomology of a bounded-below complex is homology of its derived global sections. -/
theorem hypercohomologyFunctor_obj
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) (p : ℤ) :
    (hypercohomologyFunctor X p).obj K =
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} p).obj
        ((functor (siteAbelianSectionsFunctor X.smallEtaleTopology (globalEtale X))).obj K) :=
  rfl

/-- The map on hypercohomology is the homology map of the induced map on derived global sections. -/
theorem hypercohomologyFunctor_map (p : ℤ)
    {K L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})} (f : K ⟶ L) :
    (hypercohomologyFunctor X p).map f =
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} p).map
        ((functor (siteAbelianSectionsFunctor X.smallEtaleTopology (globalEtale X))).map f) :=
  rfl

end AlgebraicGeometry.Scheme.Etale.BoundedBelow

end

end
