/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.Adjunction.Derived.Bounded
public import ReasLib.CategoryTheory.Adjunction.Derived.Unbounded
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Square
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
public import ReasLib.CategoryTheory.Sites.Over.Adjunction
public import ReasLib.CategoryTheory.Sites.Over.Derived.Unbounded
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.BoundedBelow
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.ZMod
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.Adjunction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Small-to-big étale pushforward comparisons

Canonical mates identifying small étale direct images with big étale direct images after
`π⁻¹`, at the level of sheaves of sets and of derived categories of abelian and `ZMod n`
coefficients.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Hom
open CategoryTheory.Sheaf
open scoped MorphismOfTopoiIn

noncomputable section

universe w u v

namespace AlgebraicGeometry.Scheme.Etale.SmallToBig

variable {S T : Scheme.{u}}

section
variable {f : T ⟶ S}

/-- Continuous sheaf pushforward along `Over.pullback f` on big étale sites is a right adjoint,
via `etaleTopology.overMapPushforwardAdjunction`. -/
instance isRightAdjoint_overPullback_sheafPushforwardContinuous
    {A : Type v} [Category A] :
    ((Over.pullback f).sheafPushforwardContinuous A
      (S.overGrothendieckTopology @Etale)
      (T.overGrothendieckTopology @Etale)).IsRightAdjoint :=
  (Scheme.etaleTopology.overMapPushforwardAdjunction A f).isRightAdjoint

/-- The composite `smallEtalePullback f ⋙ relocalizationFunctor (𝟙 T)` is continuous from the
small étale topology of `S` to the big étale topology of `T`. -/
instance isContinuous_smallEtalePullback_comp_relocalization :
    Functor.IsContinuous (smallEtalePullback f ⋙ relocalizationFunctor (𝟙 T))
      S.smallEtaleTopology (T.overGrothendieckTopology @Etale) :=
  Functor.isContinuous_comp (smallEtalePullback f) (relocalizationFunctor (𝟙 T))
    S.smallEtaleTopology T.smallEtaleTopology (T.overGrothendieckTopology @Etale)

end

variable (f : T ⟶ S)

/-- Site-level identification of the two paths around the small/big étale square, using
`MorphismProperty.Over.pullbackCompForgetIso` and identity reindexing on slices. -/
noncomputable def smallBigRelocalizationSiteIso :
    smallEtalePullback f ⋙ relocalizationFunctor (𝟙 T) ≅
      relocalizationFunctor (𝟙 S) ⋙ Over.pullback f :=
  (Functor.associator (smallEtalePullback f)
      (MorphismProperty.Over.forget (@Etale) ⊤ T) (Over.map (𝟙 T))).symm ≪≫
    Functor.isoWhiskerRight
      (MorphismProperty.Over.pullbackCompForgetIso (P := @Etale) (Q := ⊤) f)
      (Over.map (𝟙 T)) ≪≫
    Functor.associator
      (MorphismProperty.Over.forget (@Etale) ⊤ S) (Over.pullback f) (Over.map (𝟙 T)) ≪≫
    Functor.isoWhiskerLeft (MorphismProperty.Over.forget (@Etale) ⊤ S)
      (Functor.isoWhiskerLeft (Over.pullback f) (Over.mapId T) ≪≫
        Functor.rightUnitor (Over.pullback f)) ≪≫
    Functor.isoWhiskerLeft (MorphismProperty.Over.forget (@Etale) ⊤ S)
      ((Functor.leftUnitor (Over.pullback f)).symm ≪≫
        Functor.isoWhiskerRight (Over.mapId S).symm (Over.pullback f)) ≪≫
    (Functor.associator (MorphismProperty.Over.forget (@Etale) ⊤ S)
      (Over.map (𝟙 S)) (Over.pullback f)).symm

/-- The inverse image of the big étale morphism of topoi is the sheaf pullback along
`Over.pullback f`. -/
noncomputable def bigInverseImageIsoPullback :
    (Big.morphismOfTopoi f)⁻¹ ≅
      (Over.pullback f).sheafPullback (Type (u + 1))
        (S.overGrothendieckTopology @Etale) (T.overGrothendieckTopology @Etale) :=
  Adjunction.leftAdjointUniq
    (Scheme.etaleTopology.overMapPushforwardAdjunction (Type (u + 1)) f)
    ((Over.pullback f).sheafAdjunctionContinuous (Type (u + 1))
      (S.overGrothendieckTopology @Etale) (T.overGrothendieckTopology @Etale))

section TypeSheaves

variable [HasSheafify T.smallEtaleTopology (Type (u + 1))]
variable [HasSheafify S.smallEtaleTopology (Type (u + 1))]

/-- Inverse-image square `π_S⁻¹ ⋙ f_big⁻¹ ≅ f_small⁻¹ ⋙ π_T⁻¹` on sheaves of sets. -/
noncomputable def smallBigInverseImageSquare :
    (siteMorphismOfTopoi S)⁻¹ ⋙ (Big.morphismOfTopoi f)⁻¹ ≅
      (smallMorphism f)⁻¹ ⋙ (siteMorphismOfTopoi T)⁻¹ :=
  let adjπS :=
    (relocalizationFunctor (𝟙 S)).sheafAdjunctionContinuous (Type (u + 1))
      S.smallEtaleTopology (S.overGrothendieckTopology @Etale)
  let adjπT :=
    (relocalizationFunctor (𝟙 T)).sheafAdjunctionContinuous (Type (u + 1))
      T.smallEtaleTopology (T.overGrothendieckTopology @Etale)
  let adjSmall :=
    (smallEtalePullback f).sheafAdjunctionContinuous (Type (u + 1))
      S.smallEtaleTopology T.smallEtaleTopology
  let adjBigCont :=
    (Over.pullback f).sheafAdjunctionContinuous (Type (u + 1))
      (S.overGrothendieckTopology @Etale) (T.overGrothendieckTopology @Etale)
  Functor.isoWhiskerLeft ((siteMorphismOfTopoi S)⁻¹) (bigInverseImageIsoPullback f) ≪≫
    Adjunction.leftAdjointCompIso adjπS adjBigCont (adjSmall.comp adjπT)
      (Functor.sheafPushforwardContinuousComp'
          (smallBigRelocalizationSiteIso f).symm (Type (u + 1))
          S.smallEtaleTopology (S.overGrothendieckTopology @Etale)
          (T.overGrothendieckTopology @Etale) ≪≫
        (Functor.sheafPushforwardContinuousComp'
          (Iso.refl (smallEtalePullback f ⋙ relocalizationFunctor (𝟙 T)))
          (Type (u + 1)) S.smallEtaleTopology T.smallEtaleTopology
          (T.overGrothendieckTopology @Etale)).symm)

/-- Canonical Type-valued mate `π_S⁻¹ ∘ f_small,* ⟶ f_big,* ∘ π_T⁻¹`. -/
noncomputable def smallBigPushforwardHom :
    (smallMorphism f).pushforward ⋙ (siteMorphismOfTopoi S)⁻¹ ⟶
      (siteMorphismOfTopoi T)⁻¹ ⋙ (Big.morphismOfTopoi f).pushforward :=
  DerivedBaseChange.map
    (smallMorphism f).adjunction
    (Big.morphismOfTopoi f).adjunction
    (smallBigInverseImageSquare f)


end TypeSheaves

/-- Direct image of abelian sheaves along the big étale morphism of `f`. -/
noncomputable abbrev bigAbelianPushforward
    [∀ P : (Over T)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (Over.map f).op.HasPointwiseRightKanExtension P] :
    Sheaf (T.overGrothendieckTopology @Etale) AddCommGrpCat.{u} ⥤
      Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u} :=
  (Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u}
    (T.overGrothendieckTopology @Etale) (S.overGrothendieckTopology @Etale)

/-- Inverse image of abelian sheaves along the big étale morphism of `f`. -/
noncomputable abbrev bigAbelianInverseImage :
    Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u} ⥤
      Sheaf (T.overGrothendieckTopology @Etale) AddCommGrpCat.{u} :=
  Scheme.etaleTopology.overMapPullback AddCommGrpCat.{u} f

section AbelianSheaves

variable [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}]
variable [HasSheafify (T.overGrothendieckTopology @Etale) AddCommGrpCat.{u}]
variable [∀ P : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
    (relocalizationFunctor (𝟙 S)).op.HasLeftKanExtension P]
variable [∀ P : T.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
    (relocalizationFunctor (𝟙 T)).op.HasLeftKanExtension P]
variable [∀ P : (Over T)ᵒᵖ ⥤ AddCommGrpCat.{u},
    (Over.map f).op.HasPointwiseRightKanExtension P]

/-- Inverse-image square `π_S⁻¹ ⋙ f_big⁻¹ ≅ f_small⁻¹ ⋙ π_T⁻¹` on abelian sheaves. -/
noncomputable def abelianSmallBigInverseImageSquare :
    etalePiInverseImage S ⋙ bigAbelianInverseImage f ≅
      etaleAbelianSheafPullback f ⋙ etalePiInverseImage T :=
  let adjBig :=
    Scheme.etaleTopology.overMapPushforwardAdjunction AddCommGrpCat.{u} f
  let adjπS := etalePiAdjunction S
  let adjπT := etalePiAdjunction T
  let adjSmall :=
    (smallEtalePullback f).sheafAdjunctionContinuous AddCommGrpCat.{u}
      S.smallEtaleTopology T.smallEtaleTopology
  let adjBigCont :=
    (Over.pullback f).sheafAdjunctionContinuous AddCommGrpCat.{u}
      (S.overGrothendieckTopology @Etale) (T.overGrothendieckTopology @Etale)
  let isoPullback :
      bigAbelianInverseImage f ≅
        (Over.pullback f).sheafPullback AddCommGrpCat.{u}
          (S.overGrothendieckTopology @Etale) (T.overGrothendieckTopology @Etale) :=
    Adjunction.leftAdjointUniq adjBig adjBigCont
  Functor.isoWhiskerLeft (etalePiInverseImage S) isoPullback ≪≫
    Adjunction.leftAdjointCompIso adjπS adjBigCont (adjSmall.comp adjπT)
      (Functor.sheafPushforwardContinuousComp'
          (smallBigRelocalizationSiteIso f).symm AddCommGrpCat.{u}
          S.smallEtaleTopology (S.overGrothendieckTopology @Etale)
          (T.overGrothendieckTopology @Etale) ≪≫
        (Functor.sheafPushforwardContinuousComp'
          (Iso.refl (smallEtalePullback f ⋙ relocalizationFunctor (𝟙 T)))
          AddCommGrpCat.{u} S.smallEtaleTopology T.smallEtaleTopology
          (T.overGrothendieckTopology @Etale)).symm)

/-- Canonical abelian mate `π_S⁻¹ ∘ f_small,* ⟶ f_big,* ∘ π_T⁻¹`. -/
noncomputable def abelianSmallBigPushforwardHom :
    abelianPushforwardAlong f ⋙ etalePiInverseImage S ⟶
      etalePiInverseImage T ⋙ bigAbelianPushforward f :=
  DerivedBaseChange.map
    ((smallEtalePullback f).sheafAdjunctionContinuous AddCommGrpCat.{u}
      S.smallEtaleTopology T.smallEtaleTopology)
    (Scheme.etaleTopology.overMapCocontinuousAdjunction AddCommGrpCat.{u} f)
    (abelianSmallBigInverseImageSquare f)


section AbelianDerived

variable [PreservesFiniteLimits (etalePiInverseImage S)]
variable [PreservesFiniteColimits (etalePiInverseImage S)]
variable [PreservesFiniteLimits (etalePiInverseImage T)]
variable [PreservesFiniteColimits (etalePiInverseImage T)]
variable [PreservesFiniteLimits (bigAbelianInverseImage f)]
variable [PreservesFiniteColimits (bigAbelianInverseImage f)]
variable [(abelianPushforwardAlong f).Additive]
variable [(bigAbelianPushforward f).Additive]
variable [HasDerivedCategory.{w} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory.{w} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory.{w}
    (Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u})]
variable [HasDerivedCategory.{w}
    (Sheaf (T.overGrothendieckTopology @Etale) AddCommGrpCat.{u})]

/-- Exact inverse image `π_S⁻¹` on abelian small-étale sheaves. -/
noncomputable abbrev etalePiExact (X : Scheme.{u})
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify (X.overGrothendieckTopology @Etale) AddCommGrpCat.{u}]
    [∀ P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (relocalizationFunctor (𝟙 X)).op.HasLeftKanExtension P]
    [PreservesFiniteLimits (etalePiInverseImage X)]
    [PreservesFiniteColimits (etalePiInverseImage X)] :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤ₑ
      Sheaf (X.overGrothendieckTopology @Etale) AddCommGrpCat.{u} :=
  ExactFunctor.of (etalePiInverseImage X)

/-- Exact inverse image along the big étale morphism of `f`. -/
noncomputable abbrev bigEtaleExact :
    Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u} ⥤ₑ
      Sheaf (T.overGrothendieckTopology @Etale) AddCommGrpCat.{u} :=
  ExactFunctor.of (bigAbelianInverseImage f)

/-- Bounded-below derived inverse image `π_S⁻¹` on `D⁺`. -/
noncomputable abbrev plusPiInverseImage (X : Scheme.{u})
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify (X.overGrothendieckTopology @Etale) AddCommGrpCat.{u}]
    [Abelian (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    [Abelian (Sheaf (X.overGrothendieckTopology @Etale) AddCommGrpCat.{u})]
    [HasDerivedCategory.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    [HasDerivedCategory.{w}
      (Sheaf (X.overGrothendieckTopology @Etale) AddCommGrpCat.{u})]
    [∀ P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (relocalizationFunctor (𝟙 X)).op.HasLeftKanExtension P]
    [PreservesFiniteLimits (etalePiInverseImage X)]
    [PreservesFiniteColimits (etalePiInverseImage X)] :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) ⥤
      DerivedCategory.Plus
        (Sheaf (X.overGrothendieckTopology @Etale) AddCommGrpCat.{u}) :=
  ExactFunctor.Derived.Plus.functor (etalePiExact X)

/-- Bounded-below derived inverse image along the big étale morphism of `f`. -/
noncomputable abbrev plusBigInverseImage :
    DerivedCategory.Plus
      (Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}) ⥤
      DerivedCategory.Plus
        (Sheaf (T.overGrothendieckTopology @Etale) AddCommGrpCat.{u}) :=
  ExactFunctor.Derived.Plus.functor (bigEtaleExact f)

/-- Bounded-below derived direct image along the big étale morphism of `f`. -/
noncomputable abbrev plusBigDerivedPushforward
    [(bigAbelianPushforward f).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (T.overGrothendieckTopology @Etale) AddCommGrpCat.{u}))] :
    DerivedCategory.Plus
      (Sheaf (T.overGrothendieckTopology @Etale) AddCommGrpCat.{u}) ⥤
      DerivedCategory.Plus
        (Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}) :=
  Adjunction.Derived.Plus.right (bigAbelianPushforward f)

/-- Bundled exact-functor form of the abelian inverse-image square. -/
noncomputable def abelianSmallBigExactSquare :
    (etalePiExact S).comp (bigEtaleExact f) ≅
      (etalePullbackExact.{u} f).comp (etalePiExact T) :=
  (exactFunctor
      (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})
      (Sheaf (T.overGrothendieckTopology @Etale) AddCommGrpCat.{u})).isoMk
    (abelianSmallBigInverseImageSquare f)

/-- Inverse-image square on `D⁺` induced by the abelian small/big square. -/
noncomputable def plusSmallBigInverseImageSquare :
    plusPiInverseImage S ⋙ plusBigInverseImage f ≅
      ExactFunctor.Derived.Plus.functor (etalePullbackExact.{u} f) ⋙
        plusPiInverseImage T :=
  ExactFunctor.Derived.Plus.squareIso
    (etalePiExact S) (bigEtaleExact f) (etalePullbackExact.{u} f) (etalePiExact T)
    (abelianSmallBigExactSquare f)

section PlusDerived

variable [EnoughInjectives (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})]
variable [EnoughInjectives
    (Sheaf (T.overGrothendieckTopology @Etale) AddCommGrpCat.{u})]

variable [(abelianPushforwardAlong f).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso (Sheaf T.smallEtaleTopology AddCommGrpCat.{u}))]
variable [(bigAbelianPushforward f).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (T.overGrothendieckTopology @Etale) AddCommGrpCat.{u}))]

/-- Canonical `D⁺` mate `π_S⁻¹ Rf_small,* ⟶ Rf_big,* π_T⁻¹`. -/
noncomputable def plusSmallBigPushforwardHom :
    Adjunction.Derived.Plus.right (abelianPushforwardAlong f) ⋙ plusPiInverseImage S ⟶
      plusPiInverseImage T ⋙ plusBigDerivedPushforward f :=
  DerivedBaseChange.map
    (Adjunction.Derived.Plus.adjunction (etalePullbackExact.{u} f)
      (abelianPushforwardAlong f)
      ((smallEtalePullback f).sheafAdjunctionContinuous AddCommGrpCat.{u}
        S.smallEtaleTopology T.smallEtaleTopology))
    (Adjunction.Derived.Plus.adjunction (bigEtaleExact f)
      (bigAbelianPushforward f)
      (Scheme.etaleTopology.overMapCocontinuousAdjunction AddCommGrpCat.{u} f))
    (plusSmallBigInverseImageSquare f)


end PlusDerived

section UnboundedDerived

variable [IsGrothendieckAbelian (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian
    (Sheaf (T.overGrothendieckTopology @Etale) AddCommGrpCat.{u})]

/-- Unbounded derived inverse image `π_S⁻¹`. -/
noncomputable abbrev unboundedPiInverseImage (X : Scheme.{u})
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify (X.overGrothendieckTopology @Etale) AddCommGrpCat.{u}]
    [Abelian (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    [Abelian (Sheaf (X.overGrothendieckTopology @Etale) AddCommGrpCat.{u})]
    [HasDerivedCategory.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    [HasDerivedCategory.{w}
      (Sheaf (X.overGrothendieckTopology @Etale) AddCommGrpCat.{u})]
    [∀ P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (relocalizationFunctor (𝟙 X)).op.HasLeftKanExtension P]
    [PreservesFiniteLimits (etalePiInverseImage X)]
    [PreservesFiniteColimits (etalePiInverseImage X)] :
    DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) ⥤
      DerivedCategory
        (Sheaf (X.overGrothendieckTopology @Etale) AddCommGrpCat.{u}) :=
  (etalePiExact X).mapDerivedCategory

/-- Unbounded derived inverse image along the big étale morphism of `f`. -/
noncomputable abbrev unboundedBigInverseImage :
    DerivedCategory
      (Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}) ⥤
      DerivedCategory
        (Sheaf (T.overGrothendieckTopology @Etale) AddCommGrpCat.{u}) :=
  (bigEtaleExact f).mapDerivedCategory

/-- Unbounded derived direct image along the small étale morphism of `f`. -/
noncomputable abbrev unboundedSmallDerivedPushforward
    [IsGrothendieckAbelian (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})] :
    DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u}) ⥤
      DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) :=
  Adjunction.Derived.KInjective.right (abelianPushforwardAlong f)

/-- Unbounded derived direct image along the big étale morphism of `f`. -/
noncomputable abbrev unboundedBigDerivedPushforward
    [IsGrothendieckAbelian
      (Sheaf (T.overGrothendieckTopology @Etale) AddCommGrpCat.{u})] :
    DerivedCategory
      (Sheaf (T.overGrothendieckTopology @Etale) AddCommGrpCat.{u}) ⥤
      DerivedCategory
        (Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}) :=
  Adjunction.Derived.KInjective.right (bigAbelianPushforward f)

/-- Inverse-image square on unbounded derived categories. -/
noncomputable def unboundedSmallBigInverseImageSquare :
    unboundedPiInverseImage S ⋙ unboundedBigInverseImage f ≅
      (etalePullbackExact.{u} f).mapDerivedCategory ⋙ unboundedPiInverseImage T :=
  (ExactFunctor.MapDerivedCategory.compFunctorIso
      (etalePiExact S) (bigEtaleExact f)).symm ≪≫
    ExactFunctor.MapDerivedCategory.mapIso (abelianSmallBigExactSquare f) ≪≫
    ExactFunctor.MapDerivedCategory.compFunctorIso
      (etalePullbackExact.{u} f) (etalePiExact T)

/-- Canonical unbounded derived mate `π_S⁻¹ Rf_small,* ⟶ Rf_big,* π_T⁻¹`. -/
noncomputable def unboundedSmallBigPushforwardHom :
    unboundedSmallDerivedPushforward f ⋙ unboundedPiInverseImage S ⟶
      unboundedPiInverseImage T ⋙ unboundedBigDerivedPushforward f :=
  DerivedBaseChange.map
    (Adjunction.Derived.KInjective.adjunction (etalePullbackExact.{u} f)
      (abelianPushforwardAlong f)
      ((smallEtalePullback f).sheafAdjunctionContinuous AddCommGrpCat.{u}
        S.smallEtaleTopology T.smallEtaleTopology))
    (Adjunction.Derived.KInjective.adjunction (bigEtaleExact f)
      (bigAbelianPushforward f)
      (Scheme.etaleTopology.overMapCocontinuousAdjunction AddCommGrpCat.{u} f))
    (unboundedSmallBigInverseImageSquare f)


end UnboundedDerived

end AbelianDerived

end AbelianSheaves

/-- Inverse image of small-étale `ZMod n`-module sheaves along identity-base relocalization. -/
noncomputable def zmodPiInverseImage (X : Scheme.{u}) (n : ℕ)
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify (X.overGrothendieckTopology @Etale) (ModuleCat.{u} (ZMod n))]
    [∀ P : X.Etaleᵒᵖ ⥤ ModuleCat.{u} (ZMod n),
      (relocalizationFunctor (𝟙 X)).op.HasLeftKanExtension P] :
    Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)) ⥤
      Sheaf (X.overGrothendieckTopology @Etale) (ModuleCat.{u} (ZMod n)) :=
  (relocalizationFunctor (𝟙 X)).sheafPullback (ModuleCat.{u} (ZMod n))
    X.smallEtaleTopology (X.overGrothendieckTopology @Etale)

/-- Direct image of `ZMod n`-module sheaves along the big étale morphism of `f`. -/
noncomputable abbrev zmodBigPushforward (n : ℕ)
    [∀ P : (Over T)ᵒᵖ ⥤ ModuleCat.{u} (ZMod n),
      (Over.map f).op.HasPointwiseRightKanExtension P] :
    Sheaf (T.overGrothendieckTopology @Etale) (ModuleCat.{u} (ZMod n)) ⥤
      Sheaf (S.overGrothendieckTopology @Etale) (ModuleCat.{u} (ZMod n)) :=
  (Over.map f).sheafPushforwardCocontinuous (ModuleCat.{u} (ZMod n))
    (T.overGrothendieckTopology @Etale) (S.overGrothendieckTopology @Etale)

/-- Inverse image of `ZMod n`-module sheaves along the big étale morphism of `f`. -/
noncomputable abbrev zmodBigInverseImage (n : ℕ) :
    Sheaf (S.overGrothendieckTopology @Etale) (ModuleCat.{u} (ZMod n)) ⥤
      Sheaf (T.overGrothendieckTopology @Etale) (ModuleCat.{u} (ZMod n)) :=
  Scheme.etaleTopology.overMapPullback (ModuleCat.{u} (ZMod n)) f

/-- Inverse-image square on sheaves of `ZMod n`-modules. -/
noncomputable def zmodSmallBigInverseImageSquare (n : ℕ)
    [HasSheafify S.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify T.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify (S.overGrothendieckTopology @Etale) (ModuleCat.{u} (ZMod n))]
    [HasSheafify (T.overGrothendieckTopology @Etale) (ModuleCat.{u} (ZMod n))]
    [∀ P : S.Etaleᵒᵖ ⥤ ModuleCat.{u} (ZMod n),
      (relocalizationFunctor (𝟙 S)).op.HasLeftKanExtension P]
    [∀ P : T.Etaleᵒᵖ ⥤ ModuleCat.{u} (ZMod n),
      (relocalizationFunctor (𝟙 T)).op.HasLeftKanExtension P]
    [((smallEtalePullback f).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint] :
    zmodPiInverseImage S n ⋙ zmodBigInverseImage f n ≅
      zmodSheafPullback f n ⋙ zmodPiInverseImage T n :=
  let adjBig :=
    Scheme.etaleTopology.overMapPushforwardAdjunction (ModuleCat.{u} (ZMod n)) f
  let adjπS :=
    (relocalizationFunctor (𝟙 S)).sheafAdjunctionContinuous (ModuleCat.{u} (ZMod n))
      S.smallEtaleTopology (S.overGrothendieckTopology @Etale)
  let adjπT :=
    (relocalizationFunctor (𝟙 T)).sheafAdjunctionContinuous (ModuleCat.{u} (ZMod n))
      T.smallEtaleTopology (T.overGrothendieckTopology @Etale)
  let adjSmall := zmodSheafAdjunction f n
  let adjBigCont :=
    (Over.pullback f).sheafAdjunctionContinuous (ModuleCat.{u} (ZMod n))
      (S.overGrothendieckTopology @Etale) (T.overGrothendieckTopology @Etale)
  let isoPullback :
      zmodBigInverseImage f n ≅
        (Over.pullback f).sheafPullback (ModuleCat.{u} (ZMod n))
          (S.overGrothendieckTopology @Etale) (T.overGrothendieckTopology @Etale) :=
    Adjunction.leftAdjointUniq adjBig adjBigCont
  Functor.isoWhiskerLeft (zmodPiInverseImage S n) isoPullback ≪≫
    Adjunction.leftAdjointCompIso adjπS adjBigCont (adjSmall.comp adjπT)
      (Functor.sheafPushforwardContinuousComp'
          (smallBigRelocalizationSiteIso f).symm (ModuleCat.{u} (ZMod n))
          S.smallEtaleTopology (S.overGrothendieckTopology @Etale)
          (T.overGrothendieckTopology @Etale) ≪≫
        (Functor.sheafPushforwardContinuousComp'
          (Iso.refl (smallEtalePullback f ⋙ relocalizationFunctor (𝟙 T)))
          (ModuleCat.{u} (ZMod n)) S.smallEtaleTopology T.smallEtaleTopology
          (T.overGrothendieckTopology @Etale)).symm)

/-- Bundled exact-functor form of the `ZMod n` inverse-image square. -/
noncomputable def zmodSmallBigExactSquare (n : ℕ)
    [HasSheafify S.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify T.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify (S.overGrothendieckTopology @Etale) (ModuleCat.{u} (ZMod n))]
    [HasSheafify (T.overGrothendieckTopology @Etale) (ModuleCat.{u} (ZMod n))]
    [∀ P : S.Etaleᵒᵖ ⥤ ModuleCat.{u} (ZMod n),
      (relocalizationFunctor (𝟙 S)).op.HasLeftKanExtension P]
    [∀ P : T.Etaleᵒᵖ ⥤ ModuleCat.{u} (ZMod n),
      (relocalizationFunctor (𝟙 T)).op.HasLeftKanExtension P]
    [((smallEtalePullback f).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint]
    [PreservesFiniteLimits (zmodPiInverseImage S n)]
    [PreservesFiniteColimits (zmodPiInverseImage S n)]
    [PreservesFiniteLimits (zmodPiInverseImage T n)]
    [PreservesFiniteColimits (zmodPiInverseImage T n)]
    [PreservesFiniteLimits (zmodBigInverseImage f n)]
    [PreservesFiniteColimits (zmodBigInverseImage f n)]
    [(zmodSheafPullback f n).Additive]
    [(zmodPiInverseImage S n).Additive]
    [(zmodPiInverseImage T n).Additive]
    [(zmodBigInverseImage f n).Additive] :
    (ExactFunctor.of (zmodPiInverseImage S n)).comp
      (ExactFunctor.of (zmodBigInverseImage f n)) ≅
      (zmodPullbackExact f n).comp (ExactFunctor.of (zmodPiInverseImage T n)) :=
  (exactFunctor
      (Sheaf S.smallEtaleTopology (ModuleCat.{u} (ZMod n)))
      (Sheaf (T.overGrothendieckTopology @Etale) (ModuleCat.{u} (ZMod n)))).isoMk
    (zmodSmallBigInverseImageSquare f n)

/-- Canonical `D(T_étale, ZMod n)` mate `π_S⁻¹ Rf_small,* ⟶ Rf_big,* π_T⁻¹`. -/
noncomputable def zmodSmallBigPushforwardHom (n : ℕ)
    [NeZero n]
    [HasSheafify S.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify T.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify (S.overGrothendieckTopology @Etale) (ModuleCat.{u} (ZMod n))]
    [HasSheafify (T.overGrothendieckTopology @Etale) (ModuleCat.{u} (ZMod n))]
    [HasDerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory
      (Sheaf (S.overGrothendieckTopology @Etale) (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory
      (Sheaf (T.overGrothendieckTopology @Etale) (ModuleCat.{u} (ZMod n)))]
    [IsGrothendieckAbelian (Sheaf T.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [IsGrothendieckAbelian
      (Sheaf (T.overGrothendieckTopology @Etale) (ModuleCat.{u} (ZMod n)))]
    [∀ P : S.Etaleᵒᵖ ⥤ ModuleCat.{u} (ZMod n),
      (relocalizationFunctor (𝟙 S)).op.HasLeftKanExtension P]
    [∀ P : T.Etaleᵒᵖ ⥤ ModuleCat.{u} (ZMod n),
      (relocalizationFunctor (𝟙 T)).op.HasLeftKanExtension P]
    [∀ P : (Over T)ᵒᵖ ⥤ ModuleCat.{u} (ZMod n),
      (Over.map f).op.HasPointwiseRightKanExtension P]
    [((smallEtalePullback f).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint]
    [PreservesFiniteLimits (zmodPiInverseImage S n)]
    [PreservesFiniteColimits (zmodPiInverseImage S n)]
    [PreservesFiniteLimits (zmodPiInverseImage T n)]
    [PreservesFiniteColimits (zmodPiInverseImage T n)]
    [PreservesFiniteLimits (zmodBigInverseImage f n)]
    [PreservesFiniteColimits (zmodBigInverseImage f n)]
    [(zmodSheafPushforward f n).Additive]
    [(zmodBigPushforward f n).Additive]
    [(zmodSheafPullback f n).Additive]
    [(zmodPiInverseImage S n).Additive]
    [(zmodPiInverseImage T n).Additive]
    [(zmodBigInverseImage f n).Additive] :
    zmodDerivedPushforward f n ⋙
        (ExactFunctor.of (zmodPiInverseImage S n)).mapDerivedCategory ⟶
      (ExactFunctor.of (zmodPiInverseImage T n)).mapDerivedCategory ⋙
        Adjunction.Derived.KInjective.right (zmodBigPushforward f n) :=
  DerivedBaseChange.map
    (Adjunction.Derived.KInjective.adjunction (zmodPullbackExact f n)
      (zmodSheafPushforward f n) (zmodSheafAdjunction f n))
    (Adjunction.Derived.KInjective.adjunction
      (ExactFunctor.of (zmodBigInverseImage f n)) (zmodBigPushforward f n)
      (Scheme.etaleTopology.overMapCocontinuousAdjunction (ModuleCat.{u} (ZMod n)) f))
    ((ExactFunctor.MapDerivedCategory.compFunctorIso
        (ExactFunctor.of (zmodPiInverseImage S n))
        (ExactFunctor.of (zmodBigInverseImage f n))).symm ≪≫
      ExactFunctor.MapDerivedCategory.mapIso (zmodSmallBigExactSquare f n) ≪≫
      ExactFunctor.MapDerivedCategory.compFunctorIso
        (zmodPullbackExact f n) (ExactFunctor.of (zmodPiInverseImage T n)))


end AlgebraicGeometry.Scheme.Etale.SmallToBig

end

end
