module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import stacks_project.Chap66.Definition_66_29_1_RingedSite
public import stacks_project.Chap87.Definition_87_34_1_Site
public import stacks_project.Chap87.Lemma_87_34_4_Comparison
public import stacks_project.Chap87.Lemma_87_37_6_CountablyIndexed

/-!
# Structure sheaves on the small étale site of a formal algebraic space

On an affine étale morphism `φ : U ⟶ X`, the value of a structure sheaf at
`U_red` is the inverse-limit ring of stage global sections of any directed
affine thickening presentation of `U`. Here `U_red` is the representing affine
scheme of `U ×_X X_red`, the object of `toAffineEtale`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.MorphismProperty CategoryTheory.ObjectProperty
open AlgebraicGeometry.AffineFormalAlgebraicSpace (AffineEtaleOver)
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

variable {S : Scheme.{u}}

/-- Inverse-limit diagram of stage global-section rings: the value at `i` is
`Γ((D.obj i).left, ⊤)`, and the transition maps are `appTop` (contravariant in
`D.map`). -/
def stageGlobalSectionsFunctor {Λ : Type u} [Preorder Λ] (D : Λ ⥤ Over S) :
    Λᵒᵖ ⥤ RingCat.{u} :=
  D.op ⋙ (Over.forget S).op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat RingCat

/-- The object map of `stageGlobalSectionsFunctor D` is the global-sections ring
of the corresponding stage. -/
theorem stageGlobalSectionsFunctor_obj {Λ : Type u} [Preorder Λ] (D : Λ ⥤ Over S)
    (i : Λ) :
    (stageGlobalSectionsFunctor D).obj (op i) =
      RingCat.of Γ((D.obj i).left, ⊤) :=
  sorry

/-- The morphism map of `stageGlobalSectionsFunctor D` is `appTop` of the stage
transition. -/
theorem stageGlobalSectionsFunctor_map {Λ : Type u} [Preorder Λ] (D : Λ ⥤ Over S)
    {i j : Λ} (f : i ⟶ j) :
    (stageGlobalSectionsFunctor D).map f.op =
      RingCat.ofHom (D.map f).left.appTop.hom :=
  sorry

/-- Inverse-limit ring of stage global sections of a diagram of schemes over
`S`, as a limit in `RingCat`. -/
def stageLimitRing {Λ : Type u} [Preorder Λ] (D : Λ ⥤ Over S) : RingCat.{u} :=
  limit (stageGlobalSectionsFunctor D)

/-- Projection from the inverse-limit ring of stage global sections onto the
stage `i` ring. -/
def stageLimitRing_π {Λ : Type u} [Preorder Λ] (D : Λ ⥤ Over S) (i : Λ) :
    stageLimitRing D ⟶ (stageGlobalSectionsFunctor D).obj (op i) :=
  limit.π (stageGlobalSectionsFunctor D) (op i)

/-- `stageLimitRing_π D i` is the limit projection at `op i`. -/
theorem stageLimitRing_π_eq {Λ : Type u} [Preorder Λ] (D : Λ ⥤ Over S) (i : Λ) :
    stageLimitRing_π D i = limit.π (stageGlobalSectionsFunctor D) (op i) :=
  sorry

/-- The natural transformation of stage global-section diagrams induced by a
morphism of diagrams `(F, τ)`, acting by `appTop` on each component. -/
def stageGlobalSectionsMap {Λ Μ : Type u} [Preorder Λ] [Preorder Μ]
    {D : Λ ⥤ Over S} {E : Μ ⥤ Over S} (F : Λ ⥤ Μ) (τ : D ⟶ F ⋙ E) :
    F.op ⋙ stageGlobalSectionsFunctor E ⟶ stageGlobalSectionsFunctor D where
  app i :=
    ((Over.forget S).op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat RingCat).map
      (τ.app i.unop).op
  naturality := sorry

/-- The component of `stageGlobalSectionsMap F τ` at `op i` is `appTop` of
`τ.app i`. -/
theorem stageGlobalSectionsMap_app {Λ Μ : Type u} [Preorder Λ] [Preorder Μ]
    {D : Λ ⥤ Over S} {E : Μ ⥤ Over S} (F : Λ ⥤ Μ) (τ : D ⟶ F ⋙ E) (i : Λ) :
    (stageGlobalSectionsMap F τ).app (op i) =
      RingCat.ofHom (τ.app i).left.appTop.hom :=
  sorry

/-- The morphism of inverse-limit rings induced by a morphism of diagrams
`(F, τ)`. -/
def stageLimitRing.map {Λ Μ : Type u} [Preorder Λ] [Preorder Μ]
    {D : Λ ⥤ Over S} {E : Μ ⥤ Over S} (F : Λ ⥤ Μ) (τ : D ⟶ F ⋙ E) :
    stageLimitRing E ⟶ stageLimitRing D :=
  limit.pre (stageGlobalSectionsFunctor E) F.op ≫
    limMap (stageGlobalSectionsMap F τ)

/-- `stageLimitRing.map F τ` is `limit.pre` followed by `limMap` of
`stageGlobalSectionsMap F τ`. -/
theorem stageLimitRing.map_eq {Λ Μ : Type u} [Preorder Λ] [Preorder Μ]
    {D : Λ ⥤ Over S} {E : Μ ⥤ Over S} (F : Λ ⥤ Μ) (τ : D ⟶ F ⋙ E) :
    stageLimitRing.map F τ =
      limit.pre (stageGlobalSectionsFunctor E) F.op ≫
        limMap (stageGlobalSectionsMap F τ) :=
  sorry

/-- The value of a ring sheaf on the affine étale object `U_red`. -/
abbrev structureSheafSections {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [Reduction X]
    (𝒪 : Sheaf (smallEtaleTopology X) RingCat.{u})
    (U : AffineEtaleOver X) : RingCat.{u} :=
  𝒪.obj.obj
    (op ((AlgebraicSpace.affineEtaleInclusion (reduction X)).obj
        (toAffineEtale.obj U)))

/-- `structureSheafSections 𝒪 U` is the value of `𝒪` on the image of
`toAffineEtale.obj U` in the small étale site. -/
theorem structureSheafSections_obj {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [Reduction X]
    (𝒪 : Sheaf (smallEtaleTopology X) RingCat.{u})
    (U : AffineEtaleOver X) :
    structureSheafSections 𝒪 U =
      𝒪.obj.obj
        (op ((AlgebraicSpace.affineEtaleInclusion (reduction X)).obj
            (toAffineEtale.obj U))) :=
  sorry

/-- A colimit presentation of `X` by a diagram `D` of schemes over `S` is a
cocone on the Yoneda embedding of `D` together with a comparison morphism to
`X` that is an fppf-local isomorphism. -/
structure ColimitPresentation {S : Scheme.{u}} {Λ : Type u} [Preorder Λ]
    (D : Λ ⥤ Over S) (X : (Over S)ᵒᵖ ⥤ Type u) where
  /-- The cocone on `D ⋙ yoneda`. -/
  c : Cocone (D ⋙ yoneda)
  /-- The comparison morphism from the cocone point to `X`. -/
  η : c.pt ⟶ X
  /-- The cocone is a colimit. -/
  isColimit : IsColimit c
  /-- The comparison is fppf-locally surjective. -/
  locallySurjective : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) η
  /-- The comparison is fppf-locally injective. -/
  locallyInjective : Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) η

/-- Package a Yoneda-cocone comparison that is an fppf-local isomorphism as a
colimit presentation. -/
def ColimitPresentation.ofCocone {Λ : Type u} [Preorder Λ]
    {D : Λ ⥤ Over S} {X : (Over S)ᵒᵖ ⥤ Type u}
    (c : Cocone (D ⋙ yoneda)) (η : c.pt ⟶ X) (isColimit : IsColimit c)
    (locallySurjective :
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) η)
    (locallyInjective :
      Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) η) :
    ColimitPresentation D X where
  c := c
  η := η
  isColimit := isColimit
  locallySurjective := locallySurjective
  locallyInjective := locallyInjective

/-- Unpack a colimit presentation as a colimit cocone whose comparison to `X`
is an fppf-local isomorphism. -/
theorem ColimitPresentation.spec {Λ : Type u} [Preorder Λ]
    {D : Λ ⥤ Over S} {X : (Over S)ᵒᵖ ⥤ Type u}
    (w : ColimitPresentation D X) :
    Nonempty (IsColimit w.c) ∧
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) w.η ∧
        Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) w.η :=
  sorry

/-- Compatibility of a morphism of affine étale domains with a morphism of
directed affine thickening presentations, relative to chosen colimit
presentation witnesses. -/
structure IsCompatiblePresentation {X : (Over S)ᵒᵖ ⥤ Type u}
    {U V : AffineEtaleOver X} {Λ Λ' : Type u} [Preorder Λ] [Preorder Λ']
    {D : Λ ⥤ Over S} {D' : Λ' ⥤ Over S}
    (wU : ColimitPresentation D U.obj.left)
    (wV : ColimitPresentation D' V.obj.left)
    (ψ : U.obj.left ⟶ V.obj.left) (F : Λ ⥤ Λ') (τ : D ⟶ F ⋙ D') : Prop where
  /-- `ψ` is a morphism of domains over `X`. -/
  over : ψ ≫ V.obj.hom = U.obj.hom
  /-- The chosen colimit witnesses intertwine `τ` with `ψ`. -/
  intertwines :
    ∀ i, yoneda.map (τ.app i) ≫ wV.c.ι.app (F.obj i) ≫ wV.η =
      wU.c.ι.app i ≫ wU.η ≫ ψ

/-- Exhibit a compatible presentation morphism from a morphism over `X` and
the intertwining of the chosen presentation witnesses with `τ`. -/
def IsCompatiblePresentation.of {X : (Over S)ᵒᵖ ⥤ Type u}
    {U V : AffineEtaleOver X} {Λ Λ' : Type u} [Preorder Λ] [Preorder Λ']
    {D : Λ ⥤ Over S} {D' : Λ' ⥤ Over S}
    (wU : ColimitPresentation D U.obj.left)
    (wV : ColimitPresentation D' V.obj.left)
    (ψ : U.obj.left ⟶ V.obj.left) (F : Λ ⥤ Λ') (τ : D ⟶ F ⋙ D')
    (over : ψ ≫ V.obj.hom = U.obj.hom)
    (intertwines :
      ∀ i, yoneda.map (τ.app i) ≫ wV.c.ι.app (F.obj i) ≫ wV.η =
        wU.c.ι.app i ≫ wU.η ≫ ψ) :
    IsCompatiblePresentation wU wV ψ F τ where
  over := over
  intertwines := intertwines

/-- Unpack `IsCompatiblePresentation` as a morphism over `X` together with
the component square for the chosen presentation witnesses. -/
theorem IsCompatiblePresentation.iff {X : (Over S)ᵒᵖ ⥤ Type u}
    {U V : AffineEtaleOver X} {Λ Λ' : Type u} [Preorder Λ] [Preorder Λ']
    {D : Λ ⥤ Over S} {D' : Λ' ⥤ Over S}
    (wU : ColimitPresentation D U.obj.left)
    (wV : ColimitPresentation D' V.obj.left)
    (ψ : U.obj.left ⟶ V.obj.left) (F : Λ ⥤ Λ') (τ : D ⟶ F ⋙ D') :
    IsCompatiblePresentation wU wV ψ F τ ↔
      ψ ≫ V.obj.hom = U.obj.hom ∧
        ∀ i, yoneda.map (τ.app i) ≫ wV.c.ι.app (F.obj i) ≫ wV.η =
          wU.c.ι.app i ≫ wU.η ≫ ψ :=
  sorry

/-- A sheaf of rings on the small étale site of a formal algebraic space is a
structure sheaf when its value on each `U_red` is the inverse-limit ring of
stage global sections of any directed affine thickening presentation of `U`,
naturally in morphisms of `AffineEtaleOver` relative to chosen colimit
presentation witnesses. -/
class IsStructureSheaf {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [Reduction X]
    (𝒪 : Sheaf (smallEtaleTopology X) RingCat.{u}) : Prop where
  /-- Inverse-limit identifications `𝒪(U_red) ≅ lim Γ(U_λ)` depending on a
  colimit presentation witness, natural in compatible presentation morphisms. -/
  sectionsLimit :
    ∃ η :
      ∀ (U : AffineEtaleOver X) {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
        (D : Λ ⥤ Over S) [IsDirectedAffineThickeningColimit D U.obj.left],
        ColimitPresentation D U.obj.left →
          (structureSheafSections 𝒪 U ≅ stageLimitRing D),
      ∀ {U V : AffineEtaleOver X} (f : U ⟶ V)
        {Λ Λ' : Type u} [Preorder Λ] [Preorder Λ']
        [IsDirected Λ (· ≤ ·)] [IsDirected Λ' (· ≤ ·)]
        (D : Λ ⥤ Over S) (D' : Λ' ⥤ Over S)
        [IsDirectedAffineThickeningColimit D U.obj.left]
        [IsDirectedAffineThickeningColimit D' V.obj.left]
        (wU : ColimitPresentation D U.obj.left)
        (wV : ColimitPresentation D' V.obj.left)
        (F : Λ ⥤ Λ') (τ : D ⟶ F ⋙ D'),
        IsCompatiblePresentation wU wV f.hom.left F τ →
          𝒪.obj.map
              ((AlgebraicSpace.affineEtaleInclusion (reduction X)).map
                (toAffineEtale.map f)).op ≫
            (η U D wU).hom =
            (η V D' wV).hom ≫ stageLimitRing.map F τ

/-- Unpack `IsStructureSheaf` as one family of inverse-limit identifications
depending on a colimit presentation witness, together with the restriction
square against `stageLimitRing.map`. -/
theorem IsStructureSheaf.spec {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [Reduction X]
    (𝒪 : Sheaf (smallEtaleTopology X) RingCat.{u})
    [h𝒪 : IsStructureSheaf 𝒪] :
    ∃ η :
      ∀ (U : AffineEtaleOver X) {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
        (D : Λ ⥤ Over S) [IsDirectedAffineThickeningColimit D U.obj.left],
        ColimitPresentation D U.obj.left →
          (structureSheafSections 𝒪 U ≅ stageLimitRing D),
      ∀ {U V : AffineEtaleOver X} (f : U ⟶ V)
        {Λ Λ' : Type u} [Preorder Λ] [Preorder Λ']
        [IsDirected Λ (· ≤ ·)] [IsDirected Λ' (· ≤ ·)]
        (D : Λ ⥤ Over S) (D' : Λ' ⥤ Over S)
        [IsDirectedAffineThickeningColimit D U.obj.left]
        [IsDirectedAffineThickeningColimit D' V.obj.left]
        (wU : ColimitPresentation D U.obj.left)
        (wV : ColimitPresentation D' V.obj.left)
        (F : Λ ⥤ Λ') (τ : D ⟶ F ⋙ D'),
        IsCompatiblePresentation wU wV f.hom.left F τ →
          𝒪.obj.map
              ((AlgebraicSpace.affineEtaleInclusion (reduction X)).map
                (toAffineEtale.map f)).op ≫
            (η U D wU).hom =
            (η V D' wV).hom ≫ stageLimitRing.map F τ :=
  sorry

/-- An affine reduced scheme, viewed as a formal algebraic space, carries the
ordinary étale structure sheaf of its reduction as a structure sheaf. -/
instance instIsStructureSheaf_yoneda (U : Over S) [IsAffine U.left]
    [IsReduced U.left] [Reduction (yoneda.obj U)] :
    IsStructureSheaf
      (AlgebraicSpace.structureSheaf (reduction (yoneda.obj U))) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
