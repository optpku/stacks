/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Elements
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Square
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Pseudofunctor
public import ReasLib.CategoryTheory.Fibered.Groupoids.UnderlyingFunctorIso
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.RepresentedSections
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.SmallEtaleComparison
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.SpaceComparisonGeometry
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Sheafification
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage

/-!
# Comparison square of ringed topoi for a morphism of representing algebraic spaces

A 1-morphism `f : X ⟶ Y` of categories fibred in groupoids over `(Sch/S)_fppf`,
with `X` and `Y` represented by algebraic spaces `F` and `G`, induces a
commutative square of ringed topoi with edges `f`, `π_F`, `π_G`, and `f_small`.
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open Opposite FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

variable {X Y : GroupoidsOver S} {F G : AlgebraicSpace S}
variable (eX : F.toGroupoids ≌ X) (eY : G.toGroupoids ≌ Y) (f : X ⟶ Y)
variable (α : (f ≫ eY.symm.hom) ≅
    (eX.symm.hom ≫ AlgebraicSpace.toGroupoids.map (moduleComparisonSpaceMorphism f eX eY)))
variable [HasSheafify (AlgebraicSpace.smallEtaleTopology F) (Type u)]
variable [HasSheafify (AlgebraicSpace.smallEtaleTopology G) (Type u)]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor F X eX).op.HasLeftKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite G)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor G Y eY).op.HasLeftKanExtension P]

/-- A presentation isomorphism identifies the represented morphism with the
recovered space morphism, after transport by the representing equivalences. -/
@[expose] def presentationTwoIso :
    eX.hom ≫ f ≅
      AlgebraicSpace.toGroupoids.map (moduleComparisonSpaceMorphism f eX eY) ≫ eY.hom :=
  (ρ_ (eX.hom ≫ f)).symm ≪≫
    Bicategory.whiskerLeftIso (eX.hom ≫ f) eY.counit.symm ≪≫
    (α_ (eX.hom ≫ f) eY.inv eY.hom).symm ≪≫
    Bicategory.whiskerRightIso (α_ eX.hom f eY.inv) eY.hom ≪≫
    Bicategory.whiskerRightIso (Bicategory.whiskerLeftIso eX.hom α) eY.hom ≪≫
    Bicategory.whiskerRightIso
      (α_ eX.hom eX.inv (AlgebraicSpace.toGroupoids.map (moduleComparisonSpaceMorphism f eX eY))).symm eY.hom ≪≫
    (α_ (eX.hom ≫ eX.inv) (AlgebraicSpace.toGroupoids.map (moduleComparisonSpaceMorphism f eX eY)) eY.hom) ≪≫
    Bicategory.whiskerRightIso eX.unit.symm
      (AlgebraicSpace.toGroupoids.map (moduleComparisonSpaceMorphism f eX eY) ≫ eY.hom) ≪≫
    λ_ (AlgebraicSpace.toGroupoids.map (moduleComparisonSpaceMorphism f eX eY) ≫ eY.hom)

/-- Restriction of an étale sheaf on `X` to `S_F` along `eX.hom`. -/
private def restrictAlongEquiv (𝒢 : Sheaf X.etaleTopology (Type u)) :
    Sheaf F.toGroupoids.etaleTopology (Type u) :=
  ((toFunctor eX.hom).sheafPushforwardContinuous (Type u)
      F.toGroupoids.etaleTopology X.etaleTopology).obj 𝒢

/-- The Type-`u` CFG Kan diagram of the restricted sheaf at `u_G(V)`. -/
private abbrev compareBigDiagOver (𝒢 : Sheaf X.etaleTopology (Type u))
    (V : AlgebraicSpace.smallEtaleSite G) :
    AlgebraicSpace.compareBigIndex (moduleComparisonSpaceMorphism f eX eY) V ⥤ Type u :=
  StructuredArrow.proj (op ((smallEtaleToGroupoids G).obj V))
      (toCartesianBasedFunctor (AlgebraicSpace.toGroupoids.map (moduleComparisonSpaceMorphism f eX eY))).toFunctor.op ⋙
    (restrictAlongEquiv eX 𝒢).obj

/-- The represented source and target provide an actual limit for the
identity-presentation diagram of the given sheaf. -/
private instance compareBigDiagOver_hasLimit (𝒢 : Sheaf X.etaleTopology (Type u))
    (V : AlgebraicSpace.smallEtaleSite G) :
    HasLimit (compareBigDiagOver eX eY f 𝒢 V) :=
  HasLimit.mk
    ⟨RepresentedDirectImage.cone
        (AlgebraicSpace.toGroupoids.map (moduleComparisonSpaceMorphism f eX eY))
        (Bicategory.Equivalence.id _) (Bicategory.Equivalence.id _)
        (restrictAlongEquiv eX 𝒢) ((smallEtaleToGroupoids G).obj V),
      RepresentedDirectImage.coneIsLimit
        (AlgebraicSpace.toGroupoids.map (moduleComparisonSpaceMorphism f eX eY))
        (Bicategory.Equivalence.id _) (Bicategory.Equivalence.id _)
        (restrictAlongEquiv eX 𝒢) ((smallEtaleToGroupoids G).obj V)⟩

/-- The Type-`u` CFG Kan diagram of `𝒢` at `u_Y(V)`. -/
private abbrev compareConjBigDiag (𝒢 : Sheaf X.etaleTopology (Type u))
    (V : AlgebraicSpace.smallEtaleSite G) :
    StructuredArrow (op ((smallEtaleFunctor G Y eY).obj V))
        (toCartesianBasedFunctor f).toFunctor.op ⥤ Type u :=
  let _ := eX
  StructuredArrow.proj (op ((smallEtaleFunctor G Y eY).obj V))
      (toCartesianBasedFunctor f).toFunctor.op ⋙
    𝒢.obj

/-- The supplied presentations give a concrete atlas descent limit of the
original CFG comma diagram. -/
private instance compareConjBigDiag_hasLimit (𝒢 : Sheaf X.etaleTopology (Type u))
    (V : AlgebraicSpace.smallEtaleSite G) :
    HasLimit (compareConjBigDiag eX eY f 𝒢 V) :=
  HasLimit.mk
    ⟨RepresentedDirectImage.cone f eX eY 𝒢 ((smallEtaleFunctor G Y eY).obj V),
      RepresentedDirectImage.coneIsLimit f eX eY 𝒢 ((smallEtaleFunctor G Y eY).obj V)⟩

/-- The Type-`u` small-étale Kan diagram of `π_{F,*} 𝒢` at `V ×_G F`. -/
private abbrev compareSmallDiagOver (𝒢 : Sheaf X.etaleTopology (Type u))
    (V : AlgebraicSpace.smallEtaleSite G) :
    AlgebraicSpace.compareSmallIndex (moduleComparisonSpaceMorphism f eX eY) V ⥤ Type u :=
  StructuredArrow.proj (op ((AlgebraicSpace.etaleBaseChange (moduleComparisonSpaceMorphism f eX eY)).obj V))
      (AlgebraicSpace.smallEtaleToSpaces F).op ⋙
    ((piToposHom F X eX).toTopos.pushforward.obj 𝒢).obj

/-- The actual small-chart extension supplies the limit of the restricted
sheaf diagram at the geometric fibre. -/
private instance compareSmallDiagOver_hasLimit (𝒢 : Sheaf X.etaleTopology (Type u))
    (V : AlgebraicSpace.smallEtaleSite G) :
    HasLimit (compareSmallDiagOver eX eY f 𝒢 V) :=
  AlgebraicSpace.EtaleTopos.allChartHasLimit F
    ((piToposHom F X eX).toTopos.pushforward.obj 𝒢)
    ((AlgebraicSpace.etaleBaseChange (moduleComparisonSpaceMorphism f eX eY)).obj V)

/-- After restriction along `compareIndexMap`, the CFG diagram is the small-étale
diagram. -/
private def compareDiagIsoOver (𝒢 : Sheaf X.etaleTopology (Type u))
    (V : AlgebraicSpace.smallEtaleSite G) :
    AlgebraicSpace.compareIndexMap (moduleComparisonSpaceMorphism f eX eY) V ⋙
        compareBigDiagOver eX eY f 𝒢 V ≅
      compareSmallDiagOver eX eY f 𝒢 V :=
  NatIso.ofComponents (fun _ => Iso.refl _) sorry

/-- Restriction of compatible families from the CFG Kan comma category to the
small-étale Kan comma category. -/
private def compareLimitHomOver (𝒢 : Sheaf X.etaleTopology (Type u))
    (V : AlgebraicSpace.smallEtaleSite G) :
    limit (compareBigDiagOver eX eY f 𝒢 V) ⟶
      limit (compareSmallDiagOver eX eY f 𝒢 V) :=
  limit.lift (compareSmallDiagOver eX eY f 𝒢 V)
    { pt := limit (compareBigDiagOver eX eY f 𝒢 V)
      π :=
        { app := fun k ↦
            limit.π (compareBigDiagOver eX eY f 𝒢 V)
                ((AlgebraicSpace.compareIndexMap (moduleComparisonSpaceMorphism f eX eY) V).obj k) ≫
              (compareDiagIsoOver eX eY f 𝒢 V).hom.app k
          naturality := sorry } }

/-- Restriction of a small-étale compatible family to the atlas cover `U₀`. -/
private def compareCoverSectionOver (𝒢 : Sheaf X.etaleTopology (Type u))
    (V : AlgebraicSpace.smallEtaleSite G) :
    limit (compareSmallDiagOver eX eY f 𝒢 V) ⟶
      (restrictAlongEquiv eX 𝒢).obj.obj
        (op ((smallEtaleToGroupoids F).obj
          (AlgebraicSpace.coverSite (moduleComparisonSpaceMorphism f eX eY) V))) :=
  limit.π (compareSmallDiagOver eX eY f 𝒢 V)
    (AlgebraicSpace.coverIndex (moduleComparisonSpaceMorphism f eX eY) V)

/-- The family of sections on the atlas pullback along the original comma
arrow into `V ×_G F`. -/
private def compareFibreSectionOver (𝒢 : Sheaf X.etaleTopology (Type u))
    (V : AlgebraicSpace.smallEtaleSite G)
    (j : AlgebraicSpace.compareBigIndex (moduleComparisonSpaceMorphism f eX eY) V) :
    limit (compareSmallDiagOver eX eY f 𝒢 V) ⟶
      (restrictAlongEquiv eX 𝒢).obj.obj
        (op (AlgebraicSpace.compareFibreObj (moduleComparisonSpaceMorphism f eX eY) j)) :=
  compareCoverSectionOver eX eY f 𝒢 V ≫
    (restrictAlongEquiv eX 𝒢).obj.map
      (AlgebraicSpace.compareFibreToCover (moduleComparisonSpaceMorphism f eX eY) j).op

/-- The atlas pullback overlap maps have equal images in `V ×_G F`, so the
small-chart compatible family has equal restrictions on their overlap. -/
private theorem compareFibreSectionOver_compatible (𝒢 : Sheaf X.etaleTopology (Type u))
    (V : AlgebraicSpace.smallEtaleSite G)
    (j : AlgebraicSpace.compareBigIndex (moduleComparisonSpaceMorphism f eX eY) V) :
    ∀ ⦃W : F.toGroupoids.total⦄ ⦃i k : Unit⦄
      (a : W ⟶ AlgebraicSpace.compareFibreObj (moduleComparisonSpaceMorphism f eX eY) j)
      (b : W ⟶ AlgebraicSpace.compareFibreObj (moduleComparisonSpaceMorphism f eX eY) j),
      a ≫ AlgebraicSpace.compareFibreToBig (moduleComparisonSpaceMorphism f eX eY) j =
          b ≫ AlgebraicSpace.compareFibreToBig (moduleComparisonSpaceMorphism f eX eY) j →
        compareFibreSectionOver eX eY f 𝒢 V j ≫
            (restrictAlongEquiv eX 𝒢).obj.map a.op =
          compareFibreSectionOver eX eY f 𝒢 V j ≫
            (restrictAlongEquiv eX 𝒢).obj.map b.op :=
  sorry

/-- Component of the reverse comparison cone at a CFG comma object. -/
private def compareInvπOver (𝒢 : Sheaf X.etaleTopology (Type u))
    (V : AlgebraicSpace.smallEtaleSite G)
    (j : AlgebraicSpace.compareBigIndex (moduleComparisonSpaceMorphism f eX eY) V) :
    limit (compareSmallDiagOver eX eY f 𝒢 V) ⟶
      (compareBigDiagOver eX eY f 𝒢 V).obj j :=
  (restrictAlongEquiv eX 𝒢).property.amalgamateOfArrows
    (fun _ : Unit => AlgebraicSpace.compareFibreToBig (moduleComparisonSpaceMorphism f eX eY) j)
    (AlgebraicSpace.compareFibre_cover_mem (moduleComparisonSpaceMorphism f eX eY) j)
    (fun _ => compareFibreSectionOver eX eY f 𝒢 V j)
    (compareFibreSectionOver_compatible eX eY f 𝒢 V j)

/-- Extension of a small-étale compatible family to a CFG compatible family. -/
private def compareLimitInvOver (𝒢 : Sheaf X.etaleTopology (Type u))
    (V : AlgebraicSpace.smallEtaleSite G) :
    limit (compareSmallDiagOver eX eY f 𝒢 V) ⟶
      limit (compareBigDiagOver eX eY f 𝒢 V) :=
  limit.lift (compareBigDiagOver eX eY f 𝒢 V)
    { pt := limit (compareSmallDiagOver eX eY f 𝒢 V)
      π :=
        { app := compareInvπOver eX eY f 𝒢 V
          naturality := sorry } }

/-- Canonical identification of the two Type-`u` Kan-extension limits at `V`. -/
private def compareLimitIsoOver (𝒢 : Sheaf X.etaleTopology (Type u))
    (V : AlgebraicSpace.smallEtaleSite G) :
    limit (compareBigDiagOver eX eY f 𝒢 V) ≅
      limit (compareSmallDiagOver eX eY f 𝒢 V) where
  hom := compareLimitHomOver eX eY f 𝒢 V
  inv := compareLimitInvOver eX eY f 𝒢 V
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The morphism `f(eX.hom(T)) ⟶ u_Y(V)` associated to a CFG comma object over `u_G(V)`. -/
private def compareConjHom (V : AlgebraicSpace.smallEtaleSite G)
    (j : AlgebraicSpace.compareBigIndex (moduleComparisonSpaceMorphism f eX eY) V) :
    (toCartesianBasedFunctor f).toFunctor.obj
        ((toFunctor eX.hom).obj j.right.unop) ⟶
      (smallEtaleFunctor G Y eY).obj V :=
  (eqToIso (cartesian_toFunctor_eq f)).hom.app ((toFunctor eX.hom).obj j.right.unop) ≫
    (ObjectProperty.FullSubbicategory.toFunctor.compIso eX.hom f).hom.app j.right.unop ≫
      (toFunctorIso (presentationTwoIso eX eY f α)).hom.app j.right.unop ≫
        (ObjectProperty.FullSubbicategory.toFunctor.compIso
            (AlgebraicSpace.toGroupoids.map (moduleComparisonSpaceMorphism f eX eY)) eY.hom).inv.app
          j.right.unop ≫
          (toFunctor eY.hom).map
            ((eqToIso (cartesian_toFunctor_eq
                (AlgebraicSpace.toGroupoids.map (moduleComparisonSpaceMorphism f eX eY)))).inv.app
                j.right.unop ≫
              j.hom.unop)

/-- Opposite form of `compareConjHom`, as a structured arrow. -/
private def compareConjArrow (V : AlgebraicSpace.smallEtaleSite G)
    (j : AlgebraicSpace.compareBigIndex (moduleComparisonSpaceMorphism f eX eY) V) :
    op ((smallEtaleFunctor G Y eY).obj V) ⟶
      (toCartesianBasedFunctor f).toFunctor.op.obj
        (op ((toFunctor eX.hom).obj j.right.unop)) :=
  (compareConjHom eX eY f α V j).op

/-- Functor from the identity-presentation CFG comma category to the comma category
computing `f_*` at `u_Y(V)`. -/
private def compareConjIndexMap (V : AlgebraicSpace.smallEtaleSite G) :
    AlgebraicSpace.compareBigIndex (moduleComparisonSpaceMorphism f eX eY) V ⥤
      StructuredArrow (op ((smallEtaleFunctor G Y eY).obj V))
        (toCartesianBasedFunctor f).toFunctor.op where
  obj j := StructuredArrow.mk (compareConjArrow eX eY f α V j)
  map {j j'} τ :=
    StructuredArrow.homMk ((toFunctor eX.hom).map τ.right.unop).op sorry
  map_id _ := sorry
  map_comp _ _ := sorry

/-- After restriction along `compareConjIndexMap`, the conjugated diagram is the
identity-presentation CFG diagram. -/
private def compareConjDiagIso (𝒢 : Sheaf X.etaleTopology (Type u))
    (V : AlgebraicSpace.smallEtaleSite G) :
    compareConjIndexMap eX eY f α V ⋙ compareConjBigDiag eX eY f 𝒢 V ≅
      compareBigDiagOver eX eY f 𝒢 V :=
  NatIso.ofComponents (fun _ => Iso.refl _) sorry

/-- Transport of a comma arrow to the recovered space morphism using the
inverse source presentation and the target presentation. -/
private def compareConjInvHom (V : AlgebraicSpace.smallEtaleSite G)
    (k : StructuredArrow (op ((smallEtaleFunctor G Y eY).obj V))
      (toCartesianBasedFunctor f).toFunctor.op) :
    (toCartesianBasedFunctor
          (AlgebraicSpace.toGroupoids.map (moduleComparisonSpaceMorphism f eX eY))).toFunctor.obj
        ((toFunctor eX.inv).obj k.right.unop) ⟶
      (smallEtaleToGroupoids G).obj V :=
  let T := (toFunctor eX.inv).obj k.right.unop
  let W := k.right.unop
  let φ := AlgebraicSpace.toGroupoids.map (moduleComparisonSpaceMorphism f eX eY)
  let yArrow :=
    (ObjectProperty.FullSubbicategory.toFunctor.compIso φ eY.hom).hom.app T ≫
      (toFunctorIso (presentationTwoIso eX eY f α).symm).hom.app T ≫
        (ObjectProperty.FullSubbicategory.toFunctor.compIso eX.hom f).inv.app T ≫
          (toFunctor f).map ((toFunctorIso eX.counit).hom.app W) ≫
            k.hom.unop
  (Iso.refl (𝟭 G.toGroupoids.total)).inv.app ((toFunctor φ).obj T) ≫
    (toFunctorIso eY.unit).hom.app ((toFunctor φ).obj T) ≫
      (ObjectProperty.FullSubbicategory.toFunctor.compIso eY.hom eY.inv).inv.app
        ((toFunctor φ).obj T) ≫
        (toFunctor eY.inv).map yArrow ≫
          (ObjectProperty.FullSubbicategory.toFunctor.compIso eY.hom eY.inv).hom.app
            ((smallEtaleToGroupoids G).obj V) ≫
            (toFunctorIso eY.unit).inv.app ((smallEtaleToGroupoids G).obj V) ≫
              (Iso.refl (𝟭 G.toGroupoids.total)).hom.app ((smallEtaleToGroupoids G).obj V)

/-- Inverse functor of `compareConjIndexMap`, sending `W` to `eX.inv(W)`. -/
private def compareConjIndexMapInv (V : AlgebraicSpace.smallEtaleSite G) :
    StructuredArrow (op ((smallEtaleFunctor G Y eY).obj V))
        (toCartesianBasedFunctor f).toFunctor.op ⥤
      AlgebraicSpace.compareBigIndex (moduleComparisonSpaceMorphism f eX eY) V where
  obj k := StructuredArrow.mk (compareConjInvHom eX eY f α V k).op
  map {k k'} τ :=
    StructuredArrow.homMk ((toFunctor eX.inv).map τ.right.unop).op sorry
  map_id _ := sorry
  map_comp _ _ := sorry

/-- Restriction along `eX.counit` after evaluating the restricted sheaf at `eX.inv(W)`. -/
private def compareConjInvπ (𝒢 : Sheaf X.etaleTopology (Type u))
    (V : AlgebraicSpace.smallEtaleSite G)
    (k : StructuredArrow (op ((smallEtaleFunctor G Y eY).obj V))
      (toCartesianBasedFunctor f).toFunctor.op) :
    limit (compareBigDiagOver eX eY f 𝒢 V) ⟶ (compareConjBigDiag eX eY f 𝒢 V).obj k :=
  let W := k.right.unop
  limit.π (compareBigDiagOver eX eY f 𝒢 V)
      ((compareConjIndexMapInv eX eY f α V).obj k) ≫
    𝒢.obj.map
      ((Iso.refl (𝟭 X.total)).inv.app W ≫
        (toFunctorIso eX.counit).inv.app W ≫
          (ObjectProperty.FullSubbicategory.toFunctor.compIso eX.inv eX.hom).inv.app W).op

/-- Canonical identification of the conjugated CFG limit with the identity-presentation
CFG limit. -/
private def compareConjLimitIso (𝒢 : Sheaf X.etaleTopology (Type u))
    (V : AlgebraicSpace.smallEtaleSite G) :
    limit (compareConjBigDiag eX eY f 𝒢 V) ≅
      limit (compareBigDiagOver eX eY f 𝒢 V) where
  hom :=
    limit.lift (compareBigDiagOver eX eY f 𝒢 V)
      { pt := limit (compareConjBigDiag eX eY f 𝒢 V)
        π :=
          { app := fun j ↦
              limit.π (compareConjBigDiag eX eY f 𝒢 V)
                  ((compareConjIndexMap eX eY f α V).obj j) ≫
                (compareConjDiagIso eX eY f α 𝒢 V).hom.app j
            naturality := sorry } }
  inv :=
    limit.lift (compareConjBigDiag eX eY f 𝒢 V)
      { pt := limit (compareBigDiagOver eX eY f 𝒢 V)
        π :=
          { app := compareConjInvπ eX eY f α 𝒢 V
            naturality := sorry } }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Evaluation of `π_{G,*} f_* 𝒢` at `V` as a CFG Kan limit of the restricted sheaf. -/
private def compareMorphismIso_leftEval (𝒢 : Sheaf X.etaleTopology (Type u))
    (V : AlgebraicSpace.smallEtaleSite G) :
    -- Local instance justification (noncanonical choice): this small-section witness is derived from the explicit representing equivalences eX and eY, which cannot be inferred from f; keep the presentation-dependent installation local.
    letI := hasSmallCFGTypeSections_ofRepresented f eX eY
    ((RingedSite.ToposHom.comp (etaleRingedToposHom f)
            (piToposHom G Y eY)).toTopos.pushforward.obj 𝒢).obj.obj (op V) ≅
      limit (compareBigDiagOver eX eY f 𝒢 V) :=
  -- Local instance justification (noncanonical choice): this small-section witness is derived from the explicit representing equivalences eX and eY, which cannot be inferred from f; keep the presentation-dependent installation local.
  letI := hasSmallCFGTypeSections_ofRepresented f eX eY
  sheafPushforwardContinuousObjObjIso (smallEtaleFunctor G Y eY) (Type u)
      ((etaleRingedToposHom f).toTopos.pushforward.obj 𝒢) V ≪≫
    (Iso.refl (limit (compareConjBigDiag eX eY f 𝒢 V))) ≪≫
      compareConjLimitIso eX eY f α 𝒢 V

/-- The spaces-étale extension of `π_{F,*} 𝒢` used by `f_small,*`. -/
private abbrev compareSmallExtendedOver (𝒢 : Sheaf X.etaleTopology (Type u)) :
    Sheaf (AlgebraicSpace.spacesEtaleTopology F) (Type u) :=
  (AlgebraicSpace.EtaleTopos.extension F).obj
    ((piToposHom F X eX).toTopos.pushforward.obj 𝒢)

/-- Evaluation of `f_small,* π_{F,*} 𝒢` at `V` recovers the small-étale Kan limit. -/
private def compareMorphismIso_rightEval (𝒢 : Sheaf X.etaleTopology (Type u))
    (V : AlgebraicSpace.smallEtaleSite G) :
    limit (compareSmallDiagOver eX eY f 𝒢 V) ≅
      ((RingedSite.ToposHom.comp (piToposHom F X eX)
            (AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism f eX eY))).toTopos.pushforward.obj
        𝒢).obj.obj (op V) :=
  ((AlgebraicSpace.EtaleTopos.allChartIsLimit F
      ((piToposHom F X eX).toTopos.pushforward.obj 𝒢)
      ((AlgebraicSpace.etaleBaseChange (moduleComparisonSpaceMorphism f eX eY)).obj V)).conePointUniqueUpToIso
    (limit.isLimit (compareSmallDiagOver eX eY f 𝒢 V))).symm

/-- Sectionwise identification of `π_{G,*} f_* 𝒢` with `f_small,* π_{F,*} 𝒢`. -/
private def compareMorphismIso_app (𝒢 : Sheaf X.etaleTopology (Type u))
    (V : AlgebraicSpace.smallEtaleSite G) :
    -- Local instance justification (noncanonical choice): this small-section witness is derived from the explicit representing equivalences eX and eY, which cannot be inferred from f; keep the presentation-dependent installation local.
    letI := hasSmallCFGTypeSections_ofRepresented f eX eY
    ((RingedSite.ToposHom.comp (etaleRingedToposHom f)
            (piToposHom G Y eY)).toTopos.pushforward.obj 𝒢).obj.obj (op V) ≅
      ((RingedSite.ToposHom.comp (piToposHom F X eX)
            (AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism f eX eY))).toTopos.pushforward.obj
        𝒢).obj.obj (op V) :=
  -- Local instance justification (noncanonical choice): this small-section witness is derived from the explicit representing equivalences eX and eY, which cannot be inferred from f; keep the presentation-dependent installation local.
  letI := hasSmallCFGTypeSections_ofRepresented f eX eY
  compareMorphismIso_leftEval eX eY f α 𝒢 V ≪≫
    compareLimitIsoOver eX eY f 𝒢 V ≪≫
      compareMorphismIso_rightEval eX eY f 𝒢 V

/-- Underlying presheaf identification of the two composites. -/
private def compareMorphismIsoPresheaf (𝒢 : Sheaf X.etaleTopology (Type u)) :
    -- Local instance justification (noncanonical choice): this small-section witness is derived from the explicit representing equivalences eX and eY, which cannot be inferred from f; keep the presentation-dependent installation local.
    letI := hasSmallCFGTypeSections_ofRepresented f eX eY
    ((RingedSite.ToposHom.comp (etaleRingedToposHom f)
            (piToposHom G Y eY)).toTopos.pushforward.obj 𝒢).obj ≅
      ((RingedSite.ToposHom.comp (piToposHom F X eX)
            (AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism f eX eY))).toTopos.pushforward.obj
        𝒢).obj :=
  -- Local instance justification (noncanonical choice): this small-section witness is derived from the explicit representing equivalences eX and eY, which cannot be inferred from f; keep the presentation-dependent installation local.
  letI := hasSmallCFGTypeSections_ofRepresented f eX eY
  NatIso.ofComponents (fun V => compareMorphismIso_app eX eY f α 𝒢 V.unop) sorry

/-- The sheaf identification `π_{G,*} f_* 𝒢 ≅ f_small,* π_{F,*} 𝒢`. -/
private def compareMorphismIso_obj (𝒢 : Sheaf X.etaleTopology (Type u)) :
    -- Local instance justification (noncanonical choice): this small-section witness is derived from the explicit representing equivalences eX and eY, which cannot be inferred from f; keep the presentation-dependent installation local.
    letI := hasSmallCFGTypeSections_ofRepresented f eX eY
    (RingedSite.ToposHom.comp (etaleRingedToposHom f)
          (piToposHom G Y eY)).toTopos.pushforward.obj 𝒢 ≅
      (RingedSite.ToposHom.comp (piToposHom F X eX)
          (AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism f eX eY))).toTopos.pushforward.obj 𝒢 :=
  -- Local instance justification (noncanonical choice): this small-section witness is derived from the explicit representing equivalences eX and eY, which cannot be inferred from f; keep the presentation-dependent installation local.
  letI := hasSmallCFGTypeSections_ofRepresented f eX eY
  {
    hom := CategoryTheory.ObjectProperty.homMk (compareMorphismIsoPresheaf eX eY f α 𝒢).hom
    inv := CategoryTheory.ObjectProperty.homMk (compareMorphismIsoPresheaf eX eY f α 𝒢).inv
    hom_inv_id := sorry
    inv_hom_id := sorry }

/-- The canonical Type-`u` identification `π_{G,*} f_* ≅ f_small,* π_{F,*}` of
direct images of ringed topoi. -/
def compareMorphismIso :
    -- Local instance justification (noncanonical choice): this small-section witness is derived from the explicit representing equivalences eX and eY, which cannot be inferred from f; keep the presentation-dependent installation local.
    letI := hasSmallCFGTypeSections_ofRepresented f eX eY
    (RingedSite.ToposHom.comp (etaleRingedToposHom f)
          (piToposHom G Y eY)).toTopos.pushforward ≅
      (RingedSite.ToposHom.comp (piToposHom F X eX)
          (AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism f eX eY))).toTopos.pushforward :=
  -- Local instance justification (noncanonical choice): this small-section witness is derived from the explicit representing equivalences eX and eY, which cannot be inferred from f; keep the presentation-dependent installation local.
  letI := hasSmallCFGTypeSections_ofRepresented f eX eY
  NatIso.ofComponents (fun 𝒢 => compareMorphismIso_obj eX eY f α 𝒢) sorry

/-- The commutative square of ringed topoi with edges `f`, `π_F`, `π_G`, and
`f_small`. -/
@[expose] def compareMorphism :
    RingedSite.ToposHom.CommSquare
      (etaleRingedSite X) (etaleRingedSite Y)
      (AlgebraicSpace.ringedSite F) (AlgebraicSpace.ringedSite G) :=
  -- Local instance justification (noncanonical choice): this small-section witness is derived from the explicit representing equivalences eX and eY, which cannot be inferred from f; keep the presentation-dependent installation local.
  letI := hasSmallCFGTypeSections_ofRepresented f eX eY
  {
    upper := etaleRingedToposHom f
    left := piToposHom F X eX
    right := piToposHom G Y eY
    lower := AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism f eX eY)
    cell :=
      { homIso := compareMorphismIso eX eY f α
        comm := sorry } }

/-- The four edges of `compareMorphism` are `f`, `π_F`, `π_G`, and `f_small`, and
the stored `2`-cell is `compareMorphismIso`. -/
theorem compareMorphism_spec :
    -- Local instance justification (noncanonical choice): this small-section witness is derived from the explicit representing equivalences eX and eY, which cannot be inferred from f; keep the presentation-dependent installation local.
    letI := hasSmallCFGTypeSections_ofRepresented f eX eY
    (compareMorphism eX eY f α).upper = etaleRingedToposHom f ∧
      (compareMorphism eX eY f α).left = piToposHom F X eX ∧
      (compareMorphism eX eY f α).right = piToposHom G Y eY ∧
      (compareMorphism eX eY f α).lower =
        AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism f eX eY) ∧
      (compareMorphism eX eY f α).cell.homIso = compareMorphismIso eX eY f α :=
  sorry

/-- The étale ringed-topos morphisms of represented categories fibred in groupoids
commute with restriction to the small étale ringed topoi of their representing spaces. -/
theorem compareMorphism_commutes :
    -- Local instance justification (noncanonical choice): this small-section witness is derived from the explicit representing equivalences eX and eY, which cannot be inferred from f; keep the presentation-dependent installation local.
    letI := hasSmallCFGTypeSections_ofRepresented f eX eY
    Nonempty (RingedSite.ToposHom.TwoIso.{u + 1, u, u + 1, u, u}
      (RingedSite.ToposHom.comp.{u + 1, u, u + 1, u, u + 1, u, u} (etaleRingedToposHom f) (piToposHom G Y eY))
      (RingedSite.ToposHom.comp.{u + 1, u, u + 1, u, u + 1, u, u} (piToposHom F X eX)
        (AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism f eX eY)))) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
