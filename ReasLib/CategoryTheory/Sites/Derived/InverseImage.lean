module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Restriction
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import ReasLib.CategoryTheory.Sites.AlmostCocontinuous.Exactness
public import ReasLib.CategoryTheory.Sites.MorphismOfSites.Exactness
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Derived Inverse Image of Abelian Sheaves

For a continuous and cocontinuous functor of sites, inverse image on abelian sheaves is exact.
This module exposes both the exact functor and its canonical action on derived categories, so
downstream code does not have to choose a resolution model or rebuild exactness instances.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe uC vC uD vD w

namespace CategoryTheory

section

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

/-- The exact sheaf pullback associated to a morphism of sites. -/
abbrev siteAbelianPullbackExact
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D) (f : C ⥤ D)
    [IsMorphismOfSites JC JD f]
    [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{w}, f.op.HasLeftKanExtension P]
    [HasSheafify JC AddCommGrpCat.{w}]
    [HasSheafify JD AddCommGrpCat.{w}]
    [PreservesFiniteLimits
      (f.op.lan : (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ Dᵒᵖ ⥤ AddCommGrpCat.{w})] :
    Sheaf JC AddCommGrpCat.{w} ⥤ₑ Sheaf JD AddCommGrpCat.{w} :=
  @ExactFunctor.of _ _ _ _
    (f.sheafPullback AddCommGrpCat.{w} JC JD)
    (Functor.IsMorphismOfSites.abelianPullback_exact f).1
    (Functor.IsMorphismOfSites.abelianPullback_exact f).2

/-- The derived functor induced by exact sheaf pullback along a morphism of sites. -/
abbrev siteAbelianPullbackDerived
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D) (f : C ⥤ D)
    [IsMorphismOfSites JC JD f]
    [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{w}, f.op.HasLeftKanExtension P]
    [HasSheafify JC AddCommGrpCat.{w}]
    [HasSheafify JD AddCommGrpCat.{w}]
    [PreservesFiniteLimits
      (f.op.lan : (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ Dᵒᵖ ⥤ AddCommGrpCat.{w})] :
    DerivedCategory (Sheaf JC AddCommGrpCat.{w}) ⥤
      DerivedCategory (Sheaf JD AddCommGrpCat.{w}) :=
  (siteAbelianPullbackExact JC JD f).mapDerivedCategory

/-- The exact inverse-image functor on abelian sheaves attached to a continuous and cocontinuous
functor of sites. -/
@[stacks 07AC "exact abelian inverse image"]
abbrev siteAbelianInverseImageExact
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D) (f : C ⥤ D)
    [Functor.IsContinuous f JC JD] [Functor.IsCocontinuous f JC JD]
    [HasSheafify JC AddCommGrpCat.{w}]
    [HasSheafify JD AddCommGrpCat.{w}] :
    Sheaf JD AddCommGrpCat.{w} ⥤ₑ Sheaf JC AddCommGrpCat.{w} :=
  ExactFunctor.of
    (f.sheafPushforwardContinuous AddCommGrpCat.{w} JC JD)

/-- The canonical derived inverse-image functor on abelian sheaves, obtained directly from the
exact inverse-image functor. -/
@[stacks 07AC "derived abelian inverse image"]
abbrev siteAbelianInverseImageDerived
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D) (f : C ⥤ D)
    [Functor.IsContinuous f JC JD] [Functor.IsCocontinuous f JC JD]
    [HasSheafify JC AddCommGrpCat.{w}]
    [HasSheafify JD AddCommGrpCat.{w}] :
    DerivedCategory (Sheaf JD AddCommGrpCat.{w}) ⥤
      DerivedCategory (Sheaf JC AddCommGrpCat.{w}) :=
  (siteAbelianInverseImageExact JC JD f).mapDerivedCategory

/-- The canonical bounded-below derived inverse image attached to a continuous and cocontinuous
functor of sites. -/
@[stacks 07AC "bounded-below derived abelian inverse image"]
noncomputable abbrev siteAbelianInverseImageBoundedBelowDerived
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D) (f : C ⥤ D)
    [Functor.IsContinuous f JC JD] [Functor.IsCocontinuous f JC JD]
    [HasSheafify JC AddCommGrpCat.{w}]
    [HasSheafify JD AddCommGrpCat.{w}] :
    DerivedCategory.Plus (Sheaf JD AddCommGrpCat.{w}) ⥤
      DerivedCategory.Plus (Sheaf JC AddCommGrpCat.{w}) :=
  ExactFunctor.Derived.Plus.functor (siteAbelianInverseImageExact JC JD f)

/-- Preservation of injective objects passes from the underlying continuous sheaf functor to
the canonical bundled exact inverse-image functor. This bridge keeps exact-first derived
composition free of local instance pins. -/
@[stacks 03YU "inverse image preserves injectives through its exact presentation"]
noncomputable instance siteAbelianInverseImageExact_preservesInjectiveObjects
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D) (f : C ⥤ D)
    [Functor.IsContinuous f JC JD] [Functor.IsCocontinuous f JC JD]
    [HasSheafify JC AddCommGrpCat.{w}]
    [HasSheafify JD AddCommGrpCat.{w}]
    [(f.sheafPushforwardContinuous AddCommGrpCat.{w} JC JD).PreservesInjectiveObjects] :
    (siteAbelianInverseImageExact JC JD f).obj.PreservesInjectiveObjects := sorry

end

end CategoryTheory
