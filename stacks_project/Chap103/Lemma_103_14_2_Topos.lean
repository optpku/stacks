/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.Topos
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.Precoverage

/-! Compatibility checks for Lemma 103.14.2. The explicit sheafification,
sheaf-composition and Kan-extension premises stand for the Stacks bounded-site
size convention. -/

@[expose] public section
open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.Functor CategoryTheory.Limits
open scoped MorphismOfTopoiIn
universe u
namespace AlgebraicGeometry.AlgebraicStack
variable {S : Scheme.{u}}

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleToposHom :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ (Type u),
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P],
    MorphismOfTopoiIn.{u + 1, u + 1, u, u, u}
      X.etaleTopology (lisseEtaleTopology X))

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleRestrictionComparison :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ (Type u),
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P],
    (lisseEtaleInclusion X).sheafPullbackCocontinuous (Type u)
        (lisseEtaleTopology X) X.etaleTopology ⟶
      (lisseEtaleInclusion X).sheafPushforwardContinuous (Type u)
        (lisseEtaleTopology X) X.etaleTopology)

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleInclusion_restriction_spec :
  ∀ (X : GroupoidsOver S)
    [AlgebraicStack X],
    (lisseEtaleInclusion X).sheafPushforwardContinuous (Type u)
          (lisseEtaleTopology X) X.etaleTopology ⋙
        sheafToPresheaf (lisseEtaleTopology X) (Type u) =
      sheafToPresheaf X.etaleTopology (Type u) ⋙
        (whiskeringLeft _ _ (Type u)).obj (lisseEtaleInclusion X).op)

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleLowerShriek :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ (Type u),
      (lisseEtaleInclusion X).op.HasLeftKanExtension P],
    Sheaf (lisseEtaleTopology X) (Type u) ⥤ Sheaf X.etaleTopology (Type u))

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleLowerShriek.adjunction :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ (Type u),
      (lisseEtaleInclusion X).op.HasLeftKanExtension P],
    lisseEtaleLowerShriek X ⊣
      (lisseEtaleInclusion X).sheafPushforwardContinuous (Type u)
        (lisseEtaleTopology X) X.etaleTopology)

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleSheafAdjunctionCocontinuous :
  ∀ (X : GroupoidsOver S)
    [AlgebraicStack X]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ (Type u),
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P],
    (lisseEtaleInclusion X).sheafPushforwardContinuous (Type u)
        (lisseEtaleTopology X) X.etaleTopology ⊣
      (lisseEtaleInclusion X).sheafPushforwardCocontinuous (Type u)
        (lisseEtaleTopology X) X.etaleTopology)

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleAbelianLowerShriek :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify X.etaleTopology AddCommGrpCat.{u}]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (lisseEtaleInclusion X).op.HasLeftKanExtension P],
    Sheaf (lisseEtaleTopology X) AddCommGrpCat.{u} ⥤
      Sheaf X.etaleTopology AddCommGrpCat.{u})

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleAbelianLowerShriek.adjunction :
  ∀ (X : GroupoidsOver S)
    [AlgebraicStack X]
    [HasSheafify X.etaleTopology AddCommGrpCat.{u}]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (lisseEtaleInclusion X).op.HasLeftKanExtension P],
    lisseEtaleAbelianLowerShriek X ⊣
      (lisseEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u}
        (lisseEtaleTopology X) X.etaleTopology)

#check (AlgebraicGeometry.AlgebraicStack.flatFppfToposHom :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ (Type u),
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P],
    MorphismOfTopoiIn.{u + 1, u + 1, u, u, u}
      (inheritedFppfTopology X) (flatFppfTopology X))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfRestrictionComparison :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ (Type u),
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P],
    (flatFppfInclusion X).sheafPullbackCocontinuous (Type u)
        (flatFppfTopology X) (inheritedFppfTopology X) ⟶
      (flatFppfInclusion X).sheafPushforwardContinuous (Type u)
        (flatFppfTopology X) (inheritedFppfTopology X))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfInclusion_restriction_spec :
  ∀ (X : GroupoidsOver S)
    [AlgebraicStack X],
    (flatFppfInclusion X).sheafPushforwardContinuous (Type u)
          (flatFppfTopology X) (inheritedFppfTopology X) ⋙
        sheafToPresheaf (flatFppfTopology X) (Type u) =
      sheafToPresheaf (inheritedFppfTopology X) (Type u) ⋙
        (whiskeringLeft _ _ (Type u)).obj (flatFppfInclusion X).op)

#check (AlgebraicGeometry.AlgebraicStack.flatFppfLowerShriek :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ (Type u),
      (flatFppfInclusion X).op.HasLeftKanExtension P],
    Sheaf (flatFppfTopology X) (Type u) ⥤
      Sheaf (inheritedFppfTopology X) (Type u))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfLowerShriek.adjunction :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ (Type u),
      (flatFppfInclusion X).op.HasLeftKanExtension P],
    flatFppfLowerShriek X ⊣
      (flatFppfInclusion X).sheafPushforwardContinuous (Type u)
        (flatFppfTopology X) (inheritedFppfTopology X))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfSheafAdjunctionCocontinuous :
  ∀ (X : GroupoidsOver S)
    [AlgebraicStack X]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ (Type u),
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P],
    (flatFppfInclusion X).sheafPushforwardContinuous (Type u)
        (flatFppfTopology X) (inheritedFppfTopology X) ⊣
      (flatFppfInclusion X).sheafPushforwardCocontinuous (Type u)
        (flatFppfTopology X) (inheritedFppfTopology X))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfAbelianLowerShriek :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (inheritedFppfTopology X) AddCommGrpCat.{u}]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (flatFppfInclusion X).op.HasLeftKanExtension P],
    Sheaf (flatFppfTopology X) AddCommGrpCat.{u} ⥤
      Sheaf (inheritedFppfTopology X) AddCommGrpCat.{u})

#check (AlgebraicGeometry.AlgebraicStack.flatFppfAbelianLowerShriek.adjunction :
  ∀ (X : GroupoidsOver S)
    [AlgebraicStack X]
    [HasSheafify (inheritedFppfTopology X) AddCommGrpCat.{u}]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (flatFppfInclusion X).op.HasLeftKanExtension P],
    flatFppfAbelianLowerShriek X ⊣
      (flatFppfInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u}
        (flatFppfTopology X) (inheritedFppfTopology X))

end AlgebraicGeometry.AlgebraicStack
