/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.AlgebraicGeometry.Scheme.LocallyClosedReduction
public import stacks_project.Chap59.Lemma_59_29_7
public import stacks_project.Chap59.Proposition_59_55_2_Over
public import stacks_project.Chap63.Definition_63_4_4_LowerShriek
public import stacks_project.Chap63.Remark_63_6_6_Forgetful

/-!
# Compactly supported direct image for pointed étale sheaves

The pointed lower/upper shriek functors along a locally quasi-finite morphism,
indexed on geometric-point fibres by `GeometricPoint.Over`. Pointed `H_Z` is
valued in `Pointed` on the existing `FiniteSupport.Admissible` poset.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]

/-- The open complement of `Z` in an ambient open in which `Z` is closed. -/
def supportComplement {W : Scheme.{u}} (Z : LocallyCloseds W) (U : W.Opens)
    (h_subset : (Z : Set W) ⊆ U)
    (h_closed : IsClosed (U.ι ⁻¹' (Z : Set W))) : W.Opens :=
  ⟨(U : Set W) \ Z, sorry⟩

/-- The support complement is contained in the ambient open. -/
theorem supportComplement_le {W : Scheme.{u}} (Z : LocallyCloseds W) (U : W.Opens)
    (h_subset : (Z : Set W) ⊆ U)
    (h_closed : IsClosed (U.ι ⁻¹' (Z : Set W))) :
    supportComplement Z U h_subset h_closed ≤ U :=
  sorry

/-- A pointed étale section on an ambient open is supported in `Z` when it
restricts to the distinguished point on the complement of `Z` in that open. -/
def IsPointedSectionSupportedIn (F : Sheaf X.smallEtaleTopology Pointed.{u})
    {W : Scheme.{u}} (hW : W ⟶ X) [Etale hW]
    (Z : LocallyCloseds W) (U : W.Opens)
    (h_subset : (Z : Set W) ⊆ U)
    (h_closed : IsClosed (U.ι ⁻¹' (Z : Set W)))
    (s : (F.1.obj (op (mk (U.ι ≫ hW)))).X) : Prop :=
  (F.1.map (FiniteSupport.homOfLE hW
      (supportComplement_le Z U h_subset h_closed)).op).toFun s =
    (F.1.obj (op (mk ((supportComplement Z U h_subset h_closed).ι ≫ hW)))).point

/-- The pointed set `H_Z(F)` of sections of `F` on the ambient open of an
admissible support that equal the distinguished point off `Z`. -/
def pointedSectionsSupportedIn (F : Sheaf X.smallEtaleTopology Pointed.{u})
    {V : Y.Etale} (A : FiniteSupport.Admissible f V) : Pointed.{u} :=
  Pointed.of
    (⟨(F.1.obj (op (mk (A.ambient.ι ≫ baseChangeToSource f V)))).point, sorry⟩ :
      { s : (F.1.obj (op (mk (A.ambient.ι ≫ baseChangeToSource f V)))).X //
        IsPointedSectionSupportedIn F (baseChangeToSource f V) A.subset A.ambient
          A.subset_le_ambient A.isClosed_in_ambient s })

/-- Membership in `H_Z(F)` is the pointed support condition on the ambient
open. -/
theorem mem_pointedSectionsSupportedIn_iff
    (F : Sheaf X.smallEtaleTopology Pointed.{u}) {V : Y.Etale}
    (A : FiniteSupport.Admissible f V)
    (s : (F.1.obj (op (mk (A.ambient.ι ≫ baseChangeToSource f V)))).X) :
    IsPointedSectionSupportedIn F (baseChangeToSource f V) A.subset A.ambient
        A.subset_le_ambient A.isClosed_in_ambient s ↔
      (F.1.map (FiniteSupport.homOfLE (baseChangeToSource f V)
          (supportComplement_le A.subset A.ambient A.subset_le_ambient
            A.isClosed_in_ambient)).op).toFun s =
        (F.1.obj (op (mk ((supportComplement A.subset A.ambient
            A.subset_le_ambient A.isClosed_in_ambient).ι ≫
          baseChangeToSource f V)))).point :=
  sorry

/-- Restriction of pointed supported sections along an inequality of admissible
supports. -/
def pointedSectionsSupportedInMap (F : Sheaf X.smallEtaleTopology Pointed.{u})
    {V : Y.Etale} {A B : FiniteSupport.Admissible f V} (h : A ≤ B) :
    pointedSectionsSupportedIn f F A ⟶ pointedSectionsSupportedIn f F B where
  toFun s :=
    ⟨(F.1.map (FiniteSupport.homOfLE (baseChangeToSource f V) h.2).op).toFun s.1, sorry⟩
  map_point := sorry

/-- The diagram of pointed sets `H_Z(F)` indexed by admissible supports on
`X_V`. -/
def pointedAdmissibleDiagram (F : Sheaf X.smallEtaleTopology Pointed.{u})
    (V : Y.Etale) : FiniteSupport.Admissible f V ⥤ Pointed.{u} where
  obj := pointedSectionsSupportedIn f F
  map h := pointedSectionsSupportedInMap f F (leOfHom h)
  map_id := sorry
  map_comp := sorry

/-- Restriction of supported sections from `X_V` to `X_{V'}`. -/
def pointedAdmissibleRestriction (F : Sheaf X.smallEtaleTopology Pointed.{u})
    {V' V : Y.Etale} (g : V' ⟶ V) :
    pointedAdmissibleDiagram f F V ⟶
      FiniteSupport.Admissible.pullbackFunctor f g ⋙
        pointedAdmissibleDiagram f F V' where
  app A :=
    { toFun := fun s ↦
        ⟨(F.1.map (FiniteSupport.preimageHom f g A.ambient).op).toFun s.1, sorry⟩
      map_point := sorry }
  naturality := sorry

variable [HasSheafify Y.smallEtaleTopology Pointed.{u}]

/-- The presheaf `f_{p!}` of pointed sets, sending `V` to the colimit of `H_Z(F)`
over admissible locally closed subsets of `|X_V|`. -/
def pointedLowerShriekPresheaf :
    Sheaf X.smallEtaleTopology Pointed.{u} ⥤ Y.Etaleᵒᵖ ⥤ Pointed.{u} where
  obj G :=
    { obj := fun V ↦ colimit (pointedAdmissibleDiagram f G V.unop)
      map := fun {V W} g ↦
        colimMap (pointedAdmissibleRestriction f G g.unop) ≫
          colimit.pre (pointedAdmissibleDiagram f G W.unop)
            (FiniteSupport.Admissible.pullbackFunctor f g.unop)
      map_id := sorry
      map_comp := sorry }
  map {G H} φ :=
    { app := fun V ↦
        colimMap
          { app := fun A ↦
              { toFun := fun s ↦
                  ⟨(φ.hom.app (op (mk (A.ambient.ι ≫
                      baseChangeToSource f V.unop)))).toFun s.1, sorry⟩
                map_point := sorry }
            naturality := sorry }
      naturality := sorry }
  map_id := sorry
  map_comp := sorry

/-- Evaluating the pointed compact-support presheaf at `V` is the colimit of
`H_Z(F)` over admissible supports on `X_V`. -/
theorem pointedLowerShriekPresheaf_obj (G : Sheaf X.smallEtaleTopology Pointed.{u})
    (V : Y.Etale) :
    ((pointedLowerShriekPresheaf f).obj G).obj (op V) =
      colimit (pointedAdmissibleDiagram f G V) :=
  sorry

/-- The pointed direct image with compact support `f_!`, obtained by
sheafifying `f_{p!}`. -/
def pointedLowerShriek :
    Sheaf X.smallEtaleTopology Pointed.{u} ⥤ Sheaf Y.smallEtaleTopology Pointed.{u} :=
  pointedLowerShriekPresheaf f ⋙ presheafToSheaf Y.smallEtaleTopology Pointed.{u}

/-- Evaluating `f_!` sheafifies the compact-support presheaf. -/
theorem pointedLowerShriek_obj (G : Sheaf X.smallEtaleTopology Pointed.{u}) :
    (pointedLowerShriek f).obj G =
      (presheafToSheaf Y.smallEtaleTopology Pointed.{u}).obj
        ((pointedLowerShriekPresheaf f).obj G) :=
  sorry

/-- The pointed compact-support functor is a left adjoint. -/
instance pointedLowerShriek_isLeftAdjoint : (pointedLowerShriek f).IsLeftAdjoint :=
  sorry

/-- The pointed upper shriek `f^!`, the chosen right adjoint of `f_!`. -/
def pointedUpperShriek :
    Sheaf Y.smallEtaleTopology Pointed.{u} ⥤ Sheaf X.smallEtaleTopology Pointed.{u} :=
  (pointedLowerShriek f).rightAdjoint

/-- The adjunction `f_! ⊣ f^!` on sheaves of pointed sets. -/
def pointedLowerShriekAdjunction : pointedLowerShriek f ⊣ pointedUpperShriek f :=
  Adjunction.ofIsLeftAdjoint (pointedLowerShriek f)

/-- The hom-equivalence of the pointed compact-support adjunction. -/
def pointedLowerShriekAdjunction_homEquiv
    (G : Sheaf X.smallEtaleTopology Pointed.{u})
    (H : Sheaf Y.smallEtaleTopology Pointed.{u}) :
    ((pointedLowerShriek f).obj G ⟶ H) ≃ (G ⟶ (pointedUpperShriek f).obj H) :=
  (pointedLowerShriekAdjunction f).homEquiv G H

/-- The fibrewise coproduct of pointed stalks at geometric points of `X` over
`ybar`. -/
def pointedStalkCoproduct (ybar : GeometricPoint Y) :
    Sheaf X.smallEtaleTopology Pointed.{u} ⥤ Pointed.{u} where
  obj G := ∐ fun x : GeometricPoint.Over f ybar ↦
    (GeometricPoint.toSmallEtalePoint x.toGeometricPoint).sheafFiber.obj G
  map {G H} φ := Limits.Sigma.map fun x : GeometricPoint.Over f ybar ↦
    (GeometricPoint.toSmallEtalePoint x.toGeometricPoint).sheafFiber.map φ
  map_id := sorry
  map_comp := sorry

/-- Evaluating the fibrewise pointed stalk coproduct recovers the coproduct of
stalks in `Pointed`. -/
theorem pointedStalkCoproduct_obj (ybar : GeometricPoint Y)
    (G : Sheaf X.smallEtaleTopology Pointed.{u}) :
    (pointedStalkCoproduct f ybar).obj G =
      ∐ fun x : GeometricPoint.Over f ybar ↦
        (GeometricPoint.toSmallEtalePoint x.toGeometricPoint).sheafFiber.obj G :=
  sorry

/-- The stalk of `f_!` at a geometric point of `Y` is the coproduct in `Pointed`
of the stalks at geometric points of `X` over `ybar`, naturally in the pointed
sheaf. -/
def pointedLowerShriekStalkIso (ybar : GeometricPoint Y) :
    pointedLowerShriek f ⋙ (GeometricPoint.toSmallEtalePoint ybar).sheafFiber ≅
      pointedStalkCoproduct f ybar :=
  Classical.choice (sorry : Nonempty
    (pointedLowerShriek f ⋙ (GeometricPoint.toSmallEtalePoint ybar).sheafFiber ≅
      pointedStalkCoproduct f ybar))

/-- The fibrewise product of pointed skyscraper sheaves at geometric points of
`X` over `ybar`. -/
def pointedSkyscraperProduct (ybar : GeometricPoint Y) :
    Pointed.{u} ⥤ Sheaf X.smallEtaleTopology Pointed.{u} where
  obj S := ∏ᶜ fun x : GeometricPoint.Over f ybar ↦
    (GeometricPoint.toSmallEtalePoint x.toGeometricPoint).skyscraperSheafFunctor.obj S
  map {S T} φ := Limits.Pi.map fun x : GeometricPoint.Over f ybar ↦
    (GeometricPoint.toSmallEtalePoint x.toGeometricPoint).skyscraperSheafFunctor.map φ
  map_id := sorry
  map_comp := sorry

/-- Evaluating the fibrewise pointed skyscraper product recovers the product of
skyscrapers. -/
theorem pointedSkyscraperProduct_obj (ybar : GeometricPoint Y) (S : Pointed.{u}) :
    (pointedSkyscraperProduct f ybar).obj S =
      ∏ᶜ fun x : GeometricPoint.Over f ybar ↦
        (GeometricPoint.toSmallEtalePoint x.toGeometricPoint).skyscraperSheafFunctor.obj S :=
  sorry

/-- `f^!` of a skyscraper at `ybar` is the product of fibre skyscrapers,
naturally in the pointed set. -/
def pointedUpperShriekSkyscraperIso (ybar : GeometricPoint Y) :
    (GeometricPoint.toSmallEtalePoint ybar).skyscraperSheafFunctor ⋙
        pointedUpperShriek f ≅
      pointedSkyscraperProduct f ybar :=
  Classical.choice (sorry : Nonempty
    ((GeometricPoint.toSmallEtalePoint ybar).skyscraperSheafFunctor ⋙
        pointedUpperShriek f ≅
      pointedSkyscraperProduct f ybar))

variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [X.smallEtaleTopology.HasSheafCompose AddCommGrpCat.toPointed]
variable [Y.smallEtaleTopology.HasSheafCompose AddCommGrpCat.toPointed]
variable [PreservesFilteredColimits AddCommGrpCat.toPointed]

/-- The fibrewise coproduct of abelian stalks at geometric points of `X` over
`ybar`. -/
def abelianStalkCoproduct (ybar : GeometricPoint Y) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} where
  obj G := ∐ fun x : GeometricPoint.Over f ybar ↦
    (GeometricPoint.toSmallEtalePoint x.toGeometricPoint).sheafFiber.obj G
  map {G H} φ := Limits.Sigma.map fun x : GeometricPoint.Over f ybar ↦
    (GeometricPoint.toSmallEtalePoint x.toGeometricPoint).sheafFiber.map φ
  map_id := sorry
  map_comp := sorry

/-- Forgetting abelian supported sections yields pointed supported sections of
the forgotten sheaf. -/
def forgetfulSupportedSections
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) {V : Y.Etale}
    (A : FiniteSupport.Admissible f V) :
    AddCommGrpCat.toPointed.obj (FiniteSupport.sections f G A) ⟶
      pointedSectionsSupportedIn f ((etaleForgetfulPointed X).obj G) A where
  toFun σ := ⟨σ.1, sorry⟩
  map_point := sorry

/-- Pointed supported sections of a forgotten abelian sheaf arise from abelian
supported sections. -/
def supportedSectionsOfForgetful
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) {V : Y.Etale}
    (A : FiniteSupport.Admissible f V) :
    pointedSectionsSupportedIn f ((etaleForgetfulPointed X).obj G) A ⟶
      AddCommGrpCat.toPointed.obj (FiniteSupport.sections f G A) where
  toFun s := ⟨s.1, sorry⟩
  map_point := sorry

/-- The diagram map induced by `AddCommGrpCat.toPointed` on
`FiniteSupport.sections`. -/
def forgetfulAdmissibleDiagram
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale) :
    FiniteSupport.diagram f G V ⋙ AddCommGrpCat.toPointed ⟶
      pointedAdmissibleDiagram f ((etaleForgetfulPointed X).obj G) V where
  app A := forgetfulSupportedSections f G A
  naturality := sorry

/-- The reverse of `forgetfulAdmissibleDiagram`, used to compare pointed
colimits with forgotten abelian colimits. -/
def forgetfulAdmissibleDiagramInv
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale) :
    pointedAdmissibleDiagram f ((etaleForgetfulPointed X).obj G) V ⟶
      FiniteSupport.diagram f G V ⋙ AddCommGrpCat.toPointed where
  app A := supportedSectionsOfForgetful f G A
  naturality := sorry

/-- The presheaf-level comparison `f_{p!} F(G) ⟶ F(f_{p!} G)`, obtained by
sending pointed supported sections to forgotten abelian supported sections and
applying the `Pointed`-vs-`AddCommGrpCat` colimit comparison. -/
def forgetfulLowerShriekPresheafComparison
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (pointedLowerShriekPresheaf f).obj ((etaleForgetfulPointed X).obj G) ⟶
      (lowerShriekPresheaf f).obj G ⋙ AddCommGrpCat.toPointed where
  app V :=
    colimMap (forgetfulAdmissibleDiagramInv f G V.unop) ≫
      colimit.post (FiniteSupport.diagram f G V.unop) AddCommGrpCat.toPointed
  naturality := sorry

/-- The canonical comparison `f_! F(G) ⟶ F(f_! G)`, the sheafification of the
sectionwise forgetful diagram map and the coefficient colimit comparison. -/
def forgetfulLowerShriekComparison :
    etaleForgetfulPointed X ⋙ pointedLowerShriek f ⟶
      lowerShriek f ⋙ etaleForgetfulPointed Y where
  app G :=
    (presheafToSheaf Y.smallEtaleTopology Pointed.{u}).map
        (forgetfulLowerShriekPresheafComparison f G) ≫
      (sheafComposeNatTrans (Y.smallEtaleTopology) AddCommGrpCat.toPointed
          (sheafificationAdjunction _ AddCommGrpCat.{u})
          (sheafificationAdjunction _ Pointed.{u})).app
        ((lowerShriekPresheaf f).obj G)
  naturality := sorry

/-- The obvious stalk-level map of the lower forgetful comparison: the pointed
coproduct of forgotten fibre stalks, compared with the forgotten abelian
coproduct via `toPointedCoprodComparison`. -/
def forgetfulLowerShriekComparisonStalk
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (z : GeometricPoint Y) :
    (pointedStalkCoproduct f z).obj ((etaleForgetfulPointed X).obj G) ⟶
      AddCommGrpCat.toPointed.obj ((abelianStalkCoproduct f z).obj G) :=
  Limits.Sigma.map (fun x : GeometricPoint.Over f z ↦
      (etaleForgetfulPointed_sheafFiberIso X x.toGeometricPoint).hom.app G) ≫
    AddCommGrpCat.toPointedCoprodComparison (fun x : GeometricPoint.Over f z ↦
      (GeometricPoint.toSmallEtalePoint x.toGeometricPoint).sheafFiber.obj G)

/-- The stalk-level comparison is `toPointedCoprodComparison` after the fibrewise
forgetful stalk isos. -/
theorem forgetfulLowerShriekComparisonStalk_eq
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (z : GeometricPoint Y) :
    forgetfulLowerShriekComparisonStalk f G z =
      Limits.Sigma.map (fun x : GeometricPoint.Over f z ↦
          (etaleForgetfulPointed_sheafFiberIso X x.toGeometricPoint).hom.app G) ≫
        AddCommGrpCat.toPointedCoprodComparison
          (fun x : GeometricPoint.Over f z ↦
            (GeometricPoint.toSmallEtalePoint x.toGeometricPoint).sheafFiber.obj G) :=
  sorry

/-- Sheafifying the sectionwise comparison recovers `forgetfulLowerShriekComparison`
on underlying presheaves. -/
theorem forgetfulLowerShriekComparison_spec
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (sheafificationAdjunction Y.smallEtaleTopology Pointed.{u}).unit.app
        ((pointedLowerShriekPresheaf f).obj ((etaleForgetfulPointed X).obj G)) ≫
      (sheafToPresheaf Y.smallEtaleTopology Pointed.{u}).map
        ((forgetfulLowerShriekComparison f).app G) =
      forgetfulLowerShriekPresheafComparison f G ≫
        Functor.whiskerRight
          ((sheafificationAdjunction Y.smallEtaleTopology AddCommGrpCat.{u}).unit.app
            ((lowerShriekPresheaf f).obj G))
          AddCommGrpCat.toPointed :=
  sorry

/-- After `pointedLowerShriekStalkIso`, the stalk of `forgetfulLowerShriekComparison`
is the obvious map `forgetfulLowerShriekComparisonStalk`. -/
theorem forgetfulLowerShriekComparison_stalk
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (z : GeometricPoint Y) :
    (pointedLowerShriekStalkIso f z).hom.app ((etaleForgetfulPointed X).obj G) ≫
        forgetfulLowerShriekComparisonStalk f G z =
      (pointedLowerShriekStalkIso f z).hom.app ((etaleForgetfulPointed X).obj G) ≫
        Limits.Sigma.map (fun x : GeometricPoint.Over f z ↦
            (etaleForgetfulPointed_sheafFiberIso X x.toGeometricPoint).hom.app G) ≫
          AddCommGrpCat.toPointedCoprodComparison
            (fun x : GeometricPoint.Over f z ↦
              (GeometricPoint.toSmallEtalePoint x.toGeometricPoint).sheafFiber.obj G) :=
  sorry

/-- The canonical comparison `F(f^! G) ⟶ f^! F(G)`, the mate of
`forgetfulLowerShriekComparison` along `lowerShriek f ⊣ abelianUpper` and
`pointedLowerShriekAdjunction`. -/
def forgetfulUpperShriekComparison
    {abelianUpper :
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} ⥤
        Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (adj : lowerShriek f ⊣ abelianUpper) :
    abelianUpper ⋙ etaleForgetfulPointed X ⟶
      etaleForgetfulPointed Y ⋙ pointedUpperShriek f :=
  mateEquiv adj (pointedLowerShriekAdjunction f) (forgetfulLowerShriekComparison f)

/-- The upper forgetful comparison is the mate of the lower forgetful square,
characterized by the adjunction counits. -/
theorem forgetfulUpperShriekComparison_spec
    {abelianUpper :
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} ⥤
        Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (adj : lowerShriek f ⊣ abelianUpper)
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (pointedLowerShriek f).map ((forgetfulUpperShriekComparison f adj).app G) ≫
        (pointedLowerShriekAdjunction f).counit.app
          ((etaleForgetfulPointed Y).obj G) =
      (forgetfulLowerShriekComparison f).app (abelianUpper.obj G) ≫
        (etaleForgetfulPointed Y).map (adj.counit.app G) :=
  sorry

/-- The transformation `F ∘ f^! ⟶ f^! ∘ F` is an isomorphism because this mate
of the lower comparison commutes with products. -/
instance forgetfulUpperShriekComparison_isIso
    {abelianUpper :
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} ⥤
        Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (adj : lowerShriek f ⊣ abelianUpper) :
    IsIso (forgetfulUpperShriekComparison f adj) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
