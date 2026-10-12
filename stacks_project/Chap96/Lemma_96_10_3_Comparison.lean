/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Elements
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Square
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Pseudofunctor
public import ReasLib.CategoryTheory.Fibered.Groupoids.UnderlyingFunctorIso
public import stacks_project.Chap96.«96_10_3_3_Comparison»

/-!
# Comparison square of ringed topoi for a morphism of representing algebraic spaces

A 1-morphism `f : X ⟶ Y` of categories fibred in groupoids over `(Sch/S)_fppf`,
with `X` and `Y` represented by algebraic spaces `F` and `G`, induces a
commutative square of ringed topoi with edges `f`, `π_F`, `π_G`, and `f_small`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open Opposite FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The morphism of algebraic spaces induced by a 1-morphism of categories fibred
in groupoids presented by `F` and `G`. -/
abbrev inducedHom {F G : AlgebraicSpace S} {X Y : GroupoidsOver S}
    (eX : F.toGroupoids ≌ X) (eY : G.toGroupoids ≌ Y) (f : X ⟶ Y) : F ⟶ G :=
  AlgebraicSpace.toGroupoids.recover eX.symm eY.symm f

/-- `inducedHom eX eY f` is recovery of `f` along `eX.symm` and `eY.symm`. -/
theorem inducedHom_eq {F G : AlgebraicSpace S} {X Y : GroupoidsOver S}
    (eX : F.toGroupoids ≌ X) (eY : G.toGroupoids ≌ Y) (f : X ⟶ Y) :
    inducedHom eX eY f = AlgebraicSpace.toGroupoids.recover eX.symm eY.symm f :=
  rfl

/-- The cartesian total functor agrees definitionally with `toFunctor`. -/
def cartesianToFunctorIso {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    (toCartesianBasedFunctor h).toFunctor ≅ toFunctor h :=
  Iso.refl _

variable {X Y : GroupoidsOver S} {F G : AlgebraicSpace S}
variable (eX : F.toGroupoids ≌ X) (eY : G.toGroupoids ≌ Y) (f : X ⟶ Y)
variable (α : (f ≫ eY.symm.hom) ≅
    (eX.symm.hom ≫ AlgebraicSpace.toGroupoids.map (inducedHom eX eY f)))
variable [HasSheafify (AlgebraicSpace.smallEtaleTopology F) (Type u)]
variable [HasSheafify (AlgebraicSpace.smallEtaleTopology G) (Type u)]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor F X eX).op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite G)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor G Y eY).op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ RingCat.{u},
    (smallEtaleFunctor F X eX).op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite G)ᵒᵖ ⥤ RingCat.{u},
    (smallEtaleFunctor G Y eY).op.HasPointwiseRightKanExtension P]
variable [(forget RingCat.{u}).PreservesRightKanExtensions (smallEtaleFunctor F X eX).op]
variable [(forget RingCat.{u}).PreservesRightKanExtensions (smallEtaleFunctor G Y eY).op]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor F X eX).op.HasLeftKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite G)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor G Y eY).op.HasLeftKanExtension P]
variable [∀ P : X.totalᵒᵖ ⥤ Type u,
    (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : F.toGroupoids.totalᵒᵖ ⥤ Type u,
    (toCartesianBasedFunctor
        (AlgebraicSpace.toGroupoids.map (inducedHom eX eY f))).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ Type u,
    (AlgebraicSpace.smallEtaleInclusion F).op.HasPointwiseRightKanExtension P]

/-- Transport of the presentation `2`-iso `α` to
`eX.hom ≫ f ≅ map(inducedHom) ≫ eY.hom` by units, counits, and associators. -/
def presentedTwoCell :
    eX.hom ≫ f ≅
      AlgebraicSpace.toGroupoids.map (inducedHom eX eY f) ≫ eY.hom :=
  (ρ_ (eX.hom ≫ f)).symm ≪≫
    Bicategory.whiskerLeftIso (eX.hom ≫ f) eY.counit.symm ≪≫
    (α_ (eX.hom ≫ f) eY.inv eY.hom).symm ≪≫
    Bicategory.whiskerRightIso (α_ eX.hom f eY.inv) eY.hom ≪≫
    Bicategory.whiskerRightIso (Bicategory.whiskerLeftIso eX.hom α) eY.hom ≪≫
    Bicategory.whiskerRightIso
      (α_ eX.hom eX.inv (AlgebraicSpace.toGroupoids.map (inducedHom eX eY f))).symm eY.hom ≪≫
    (α_ (eX.hom ≫ eX.inv) (AlgebraicSpace.toGroupoids.map (inducedHom eX eY f)) eY.hom) ≪≫
    Bicategory.whiskerRightIso eX.unit.symm
      (AlgebraicSpace.toGroupoids.map (inducedHom eX eY f) ≫ eY.hom) ≪≫
    λ_ (AlgebraicSpace.toGroupoids.map (inducedHom eX eY f) ≫ eY.hom)

/-- Restriction of an étale sheaf on `X` to `S_F` along `eX.hom`. -/
def restrictAlongEquiv (𝒢 : Sheaf X.etaleTopology (Type u)) :
    Sheaf F.toGroupoids.etaleTopology (Type u) :=
  ((toFunctor eX.hom).sheafPushforwardContinuous (Type u)
      F.toGroupoids.etaleTopology X.etaleTopology).obj 𝒢

/-- The Type-`u` CFG Kan diagram of the restricted sheaf at `u_G(V)`. -/
abbrev compareBigDiagOver (𝒢 : Sheaf X.etaleTopology (Type u))
    (V : AlgebraicSpace.smallEtaleSite G) :
    AlgebraicSpace.compareBigIndex (inducedHom eX eY f) V ⥤ Type u :=
  StructuredArrow.proj (op ((smallEtaleToGroupoids G).obj V))
      (toCartesianBasedFunctor (AlgebraicSpace.toGroupoids.map (inducedHom eX eY f))).toFunctor.op ⋙
    (restrictAlongEquiv eX 𝒢).obj

/-- The Type-`u` CFG Kan diagram of `𝒢` at `u_Y(V)`. -/
abbrev compareConjBigDiag (𝒢 : Sheaf X.etaleTopology (Type u))
    (V : AlgebraicSpace.smallEtaleSite G) :
    StructuredArrow (op ((smallEtaleFunctor G Y eY).obj V))
        (toCartesianBasedFunctor f).toFunctor.op ⥤ Type u :=
  let _ := eX
  StructuredArrow.proj (op ((smallEtaleFunctor G Y eY).obj V))
      (toCartesianBasedFunctor f).toFunctor.op ⋙
    𝒢.obj

/-- The Type-`u` small-étale Kan diagram of `π_{F,*} 𝒢` at `V ×_G F`. -/
abbrev compareSmallDiagOver (𝒢 : Sheaf X.etaleTopology (Type u))
    (V : AlgebraicSpace.smallEtaleSite G) :
    AlgebraicSpace.compareSmallIndex (inducedHom eX eY f) V ⥤ Type u :=
  StructuredArrow.proj (op ((AlgebraicSpace.etaleBaseChange (inducedHom eX eY f)).obj V))
      (AlgebraicSpace.smallEtaleInclusion F).op ⋙
    ((piToposHom F X eX).toTopos.pushforward.obj 𝒢).obj

/-- After restriction along `compareIndexMap`, the CFG diagram is the small-étale
diagram. -/
def compareDiagIsoOver (𝒢 : Sheaf X.etaleTopology (Type u))
    (V : AlgebraicSpace.smallEtaleSite G) :
    AlgebraicSpace.compareIndexMap (inducedHom eX eY f) V ⋙
        compareBigDiagOver eX eY f 𝒢 V ≅
      compareSmallDiagOver eX eY f 𝒢 V :=
  NatIso.ofComponents (fun _ => Iso.refl _) sorry

/-- Restriction of compatible families from the CFG Kan comma category to the
small-étale Kan comma category. -/
def compareLimitHomOver (𝒢 : Sheaf X.etaleTopology (Type u))
    (V : AlgebraicSpace.smallEtaleSite G) :
    limit (compareBigDiagOver eX eY f 𝒢 V) ⟶
      limit (compareSmallDiagOver eX eY f 𝒢 V) :=
  limit.lift (compareSmallDiagOver eX eY f 𝒢 V)
    { pt := limit (compareBigDiagOver eX eY f 𝒢 V)
      π :=
        { app := fun k ↦
            limit.π (compareBigDiagOver eX eY f 𝒢 V)
                ((AlgebraicSpace.compareIndexMap (inducedHom eX eY f) V).obj k) ≫
              (compareDiagIsoOver eX eY f 𝒢 V).hom.app k
          naturality := sorry } }

/-- Restriction of a small-étale compatible family to the atlas cover `U₀`. -/
def compareCoverSectionOver (𝒢 : Sheaf X.etaleTopology (Type u))
    (V : AlgebraicSpace.smallEtaleSite G) :
    limit (compareSmallDiagOver eX eY f 𝒢 V) ⟶
      (restrictAlongEquiv eX 𝒢).obj.obj
        (op ((smallEtaleToGroupoids F).obj
          (AlgebraicSpace.coverSite (inducedHom eX eY f) V))) :=
  limit.π (compareSmallDiagOver eX eY f 𝒢 V)
    (AlgebraicSpace.coverIndex (inducedHom eX eY f) V)

/-- The family of sections on `T ×_F U₀`. -/
def compareFibreSectionOver (𝒢 : Sheaf X.etaleTopology (Type u))
    (V : AlgebraicSpace.smallEtaleSite G)
    (j : AlgebraicSpace.compareBigIndex (inducedHom eX eY f) V) :
    limit (compareSmallDiagOver eX eY f 𝒢 V) ⟶
      (restrictAlongEquiv eX 𝒢).obj.obj
        (op (AlgebraicSpace.compareFibreObj (inducedHom eX eY f) j)) :=
  compareCoverSectionOver eX eY f 𝒢 V ≫
    (restrictAlongEquiv eX 𝒢).obj.map
      (AlgebraicSpace.compareFibreToCover (inducedHom eX eY f) j).op

/-- Compatibility of the one-arrow covering family on `T ×_F U₀`. -/
theorem compareFibreSectionOver_compatible (𝒢 : Sheaf X.etaleTopology (Type u))
    (V : AlgebraicSpace.smallEtaleSite G)
    (j : AlgebraicSpace.compareBigIndex (inducedHom eX eY f) V) :
    ∀ ⦃W : F.toGroupoids.total⦄ ⦃i k : Unit⦄
      (a : W ⟶ AlgebraicSpace.compareFibreObj (inducedHom eX eY f) j)
      (b : W ⟶ AlgebraicSpace.compareFibreObj (inducedHom eX eY f) j),
      a ≫ AlgebraicSpace.compareFibreToBig (inducedHom eX eY f) j =
          b ≫ AlgebraicSpace.compareFibreToBig (inducedHom eX eY f) j →
        compareFibreSectionOver eX eY f 𝒢 V j ≫
            (restrictAlongEquiv eX 𝒢).obj.map a.op =
          compareFibreSectionOver eX eY f 𝒢 V j ≫
            (restrictAlongEquiv eX 𝒢).obj.map b.op :=
  sorry

/-- Component of the reverse comparison cone at a CFG comma object. -/
def compareInvπOver (𝒢 : Sheaf X.etaleTopology (Type u))
    (V : AlgebraicSpace.smallEtaleSite G)
    (j : AlgebraicSpace.compareBigIndex (inducedHom eX eY f) V) :
    limit (compareSmallDiagOver eX eY f 𝒢 V) ⟶
      (compareBigDiagOver eX eY f 𝒢 V).obj j :=
  (restrictAlongEquiv eX 𝒢).property.amalgamateOfArrows
    (fun _ : Unit => AlgebraicSpace.compareFibreToBig (inducedHom eX eY f) j)
    (AlgebraicSpace.compareFibre_cover_mem (inducedHom eX eY f) j)
    (fun _ => compareFibreSectionOver eX eY f 𝒢 V j)
    (compareFibreSectionOver_compatible eX eY f 𝒢 V j)

/-- Extension of a small-étale compatible family to a CFG compatible family. -/
def compareLimitInvOver (𝒢 : Sheaf X.etaleTopology (Type u))
    (V : AlgebraicSpace.smallEtaleSite G) :
    limit (compareSmallDiagOver eX eY f 𝒢 V) ⟶
      limit (compareBigDiagOver eX eY f 𝒢 V) :=
  limit.lift (compareBigDiagOver eX eY f 𝒢 V)
    { pt := limit (compareSmallDiagOver eX eY f 𝒢 V)
      π :=
        { app := compareInvπOver eX eY f 𝒢 V
          naturality := sorry } }

/-- Canonical identification of the two Type-`u` Kan-extension limits at `V`. -/
def compareLimitIsoOver (𝒢 : Sheaf X.etaleTopology (Type u))
    (V : AlgebraicSpace.smallEtaleSite G) :
    limit (compareBigDiagOver eX eY f 𝒢 V) ≅
      limit (compareSmallDiagOver eX eY f 𝒢 V) where
  hom := compareLimitHomOver eX eY f 𝒢 V
  inv := compareLimitInvOver eX eY f 𝒢 V
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The morphism `f(eX.hom(T)) ⟶ u_Y(V)` associated to a CFG comma object over `u_G(V)`. -/
def compareConjHom (V : AlgebraicSpace.smallEtaleSite G)
    (j : AlgebraicSpace.compareBigIndex (inducedHom eX eY f) V) :
    (toCartesianBasedFunctor f).toFunctor.obj
        ((toFunctor eX.hom).obj j.right.unop) ⟶
      (smallEtaleFunctor G Y eY).obj V :=
  (cartesianToFunctorIso f).hom.app ((toFunctor eX.hom).obj j.right.unop) ≫
    (ObjectProperty.FullSubbicategory.toFunctor.compIso eX.hom f).hom.app j.right.unop ≫
      (toFunctorIso (presentedTwoCell eX eY f α)).hom.app j.right.unop ≫
        (ObjectProperty.FullSubbicategory.toFunctor.compIso
            (AlgebraicSpace.toGroupoids.map (inducedHom eX eY f)) eY.hom).inv.app
          j.right.unop ≫
          (toFunctor eY.hom).map
            ((cartesianToFunctorIso
                (AlgebraicSpace.toGroupoids.map (inducedHom eX eY f))).inv.app
                j.right.unop ≫
              j.hom.unop)

/-- Opposite form of `compareConjHom`, as a structured arrow. -/
def compareConjArrow (V : AlgebraicSpace.smallEtaleSite G)
    (j : AlgebraicSpace.compareBigIndex (inducedHom eX eY f) V) :
    op ((smallEtaleFunctor G Y eY).obj V) ⟶
      (toCartesianBasedFunctor f).toFunctor.op.obj
        (op ((toFunctor eX.hom).obj j.right.unop)) :=
  (compareConjHom eX eY f α V j).op

/-- Functor from the identity-presentation CFG comma category to the comma category
computing `f_*` at `u_Y(V)`. -/
def compareConjIndexMap (V : AlgebraicSpace.smallEtaleSite G) :
    AlgebraicSpace.compareBigIndex (inducedHom eX eY f) V ⥤
      StructuredArrow (op ((smallEtaleFunctor G Y eY).obj V))
        (toCartesianBasedFunctor f).toFunctor.op where
  obj j := StructuredArrow.mk (compareConjArrow eX eY f α V j)
  map {j j'} τ :=
    StructuredArrow.homMk ((toFunctor eX.hom).map τ.right.unop).op sorry
  map_id _ := sorry
  map_comp _ _ := sorry

/-- After restriction along `compareConjIndexMap`, the conjugated diagram is the
identity-presentation CFG diagram. -/
def compareConjDiagIso (𝒢 : Sheaf X.etaleTopology (Type u))
    (V : AlgebraicSpace.smallEtaleSite G) :
    compareConjIndexMap eX eY f α V ⋙ compareConjBigDiag eX eY f 𝒢 V ≅
      compareBigDiagOver eX eY f 𝒢 V :=
  NatIso.ofComponents (fun _ => Iso.refl _) sorry

/-- Identity total functor of a category fibred in groupoids. -/
def toFunctorIdIso {Z : GroupoidsOver S} : toFunctor (𝟙 Z) ≅ 𝟭 Z.total :=
  Iso.refl _

/-- The morphism `map(inducedHom)(eX.inv(W)) ⟶ u_G(V)` associated to a comma object
over `u_Y(V)`. -/
def compareConjInvHom (V : AlgebraicSpace.smallEtaleSite G)
    (k : StructuredArrow (op ((smallEtaleFunctor G Y eY).obj V))
      (toCartesianBasedFunctor f).toFunctor.op) :
    (toCartesianBasedFunctor
          (AlgebraicSpace.toGroupoids.map (inducedHom eX eY f))).toFunctor.obj
        ((toFunctor eX.inv).obj k.right.unop) ⟶
      (smallEtaleToGroupoids G).obj V :=
  let T := (toFunctor eX.inv).obj k.right.unop
  let W := k.right.unop
  let φ := AlgebraicSpace.toGroupoids.map (inducedHom eX eY f)
  let yArrow :=
    (ObjectProperty.FullSubbicategory.toFunctor.compIso φ eY.hom).hom.app T ≫
      (toFunctorIso (presentedTwoCell eX eY f α).symm).hom.app T ≫
        (ObjectProperty.FullSubbicategory.toFunctor.compIso eX.hom f).inv.app T ≫
          (toFunctor f).map ((toFunctorIso eX.counit).hom.app W) ≫
            k.hom.unop
  toFunctorIdIso.inv.app ((toFunctor φ).obj T) ≫
    (toFunctorIso eY.unit).hom.app ((toFunctor φ).obj T) ≫
      (ObjectProperty.FullSubbicategory.toFunctor.compIso eY.hom eY.inv).inv.app
        ((toFunctor φ).obj T) ≫
        (toFunctor eY.inv).map yArrow ≫
          (ObjectProperty.FullSubbicategory.toFunctor.compIso eY.hom eY.inv).hom.app
            ((smallEtaleToGroupoids G).obj V) ≫
            (toFunctorIso eY.unit).inv.app ((smallEtaleToGroupoids G).obj V) ≫
              toFunctorIdIso.hom.app ((smallEtaleToGroupoids G).obj V)

/-- Inverse functor of `compareConjIndexMap`, sending `W` to `eX.inv(W)`. -/
def compareConjIndexMapInv (V : AlgebraicSpace.smallEtaleSite G) :
    StructuredArrow (op ((smallEtaleFunctor G Y eY).obj V))
        (toCartesianBasedFunctor f).toFunctor.op ⥤
      AlgebraicSpace.compareBigIndex (inducedHom eX eY f) V where
  obj k := StructuredArrow.mk (compareConjInvHom eX eY f α V k).op
  map {k k'} τ :=
    StructuredArrow.homMk ((toFunctor eX.inv).map τ.right.unop).op sorry
  map_id _ := sorry
  map_comp _ _ := sorry

/-- Restriction along `eX.counit` after evaluating the restricted sheaf at `eX.inv(W)`. -/
def compareConjInvπ (𝒢 : Sheaf X.etaleTopology (Type u))
    (V : AlgebraicSpace.smallEtaleSite G)
    (k : StructuredArrow (op ((smallEtaleFunctor G Y eY).obj V))
      (toCartesianBasedFunctor f).toFunctor.op) :
    limit (compareBigDiagOver eX eY f 𝒢 V) ⟶ (compareConjBigDiag eX eY f 𝒢 V).obj k :=
  let W := k.right.unop
  limit.π (compareBigDiagOver eX eY f 𝒢 V)
      ((compareConjIndexMapInv eX eY f α V).obj k) ≫
    𝒢.obj.map
      (toFunctorIdIso.inv.app W ≫
        (toFunctorIso eX.counit).inv.app W ≫
          (ObjectProperty.FullSubbicategory.toFunctor.compIso eX.inv eX.hom).inv.app W).op

/-- Canonical identification of the conjugated CFG limit with the identity-presentation
CFG limit. -/
def compareConjLimitIso (𝒢 : Sheaf X.etaleTopology (Type u))
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
def compareMorphismIso_leftEval (𝒢 : Sheaf X.etaleTopology (Type u))
    (V : AlgebraicSpace.smallEtaleSite G) :
    ((RingedSite.ToposHom.comp (etaleRingedToposHom f)
            (piToposHom G Y eY)).toTopos.pushforward.obj 𝒢).obj.obj (op V) ≅
      limit (compareBigDiagOver eX eY f 𝒢 V) :=
  sheafPushforwardContinuousObjObjIso (smallEtaleFunctor G Y eY) (Type u)
      ((etaleRingedToposHom f).toTopos.pushforward.obj 𝒢) V ≪≫
    ((toCartesianBasedFunctor f).toFunctor.op.ranObjObjIsoLimit
        𝒢.obj (op ((smallEtaleFunctor G Y eY).obj V))) ≪≫
      compareConjLimitIso eX eY f α 𝒢 V

/-- The spaces-étale extension of `π_{F,*} 𝒢` used by `f_small,*`. -/
abbrev compareSmallExtendedOver (𝒢 : Sheaf X.etaleTopology (Type u)) :
    Sheaf (AlgebraicSpace.spacesEtaleTopology F) (Type u) :=
  (AlgebraicSpace.EtaleTopos.extension F).obj
    ((piToposHom F X eX).toTopos.pushforward.obj 𝒢)

/-- Evaluation of `f_small,* π_{F,*} 𝒢` at `V` recovers the small-étale Kan limit. -/
def compareMorphismIso_rightEval (𝒢 : Sheaf X.etaleTopology (Type u))
    (V : AlgebraicSpace.smallEtaleSite G) :
    limit (compareSmallDiagOver eX eY f 𝒢 V) ≅
      ((RingedSite.ToposHom.comp (piToposHom F X eX)
            (AlgebraicSpace.ringedToposHom (inducedHom eX eY f))).toTopos.pushforward.obj
        𝒢).obj.obj (op V) :=
  ((AlgebraicSpace.EtaleTopos.allChartIsLimit F
      ((piToposHom F X eX).toTopos.pushforward.obj 𝒢)
      ((AlgebraicSpace.etaleBaseChange (inducedHom eX eY f)).obj V)).conePointUniqueUpToIso
    (limit.isLimit (compareSmallDiagOver eX eY f 𝒢 V))).symm

/-- Sectionwise identification of `π_{G,*} f_* 𝒢` with `f_small,* π_{F,*} 𝒢`. -/
def compareMorphismIso_app (𝒢 : Sheaf X.etaleTopology (Type u))
    (V : AlgebraicSpace.smallEtaleSite G) :
    ((RingedSite.ToposHom.comp (etaleRingedToposHom f)
            (piToposHom G Y eY)).toTopos.pushforward.obj 𝒢).obj.obj (op V) ≅
      ((RingedSite.ToposHom.comp (piToposHom F X eX)
            (AlgebraicSpace.ringedToposHom (inducedHom eX eY f))).toTopos.pushforward.obj
        𝒢).obj.obj (op V) :=
  compareMorphismIso_leftEval eX eY f α 𝒢 V ≪≫
    compareLimitIsoOver eX eY f 𝒢 V ≪≫
      compareMorphismIso_rightEval eX eY f 𝒢 V

/-- Underlying presheaf identification of the two composites. -/
def compareMorphismIsoPresheaf (𝒢 : Sheaf X.etaleTopology (Type u)) :
    ((RingedSite.ToposHom.comp (etaleRingedToposHom f)
            (piToposHom G Y eY)).toTopos.pushforward.obj 𝒢).obj ≅
      ((RingedSite.ToposHom.comp (piToposHom F X eX)
            (AlgebraicSpace.ringedToposHom (inducedHom eX eY f))).toTopos.pushforward.obj
        𝒢).obj :=
  NatIso.ofComponents (fun V => compareMorphismIso_app eX eY f α 𝒢 V.unop) sorry

/-- The sheaf identification `π_{G,*} f_* 𝒢 ≅ f_small,* π_{F,*} 𝒢`. -/
def compareMorphismIso_obj (𝒢 : Sheaf X.etaleTopology (Type u)) :
    (RingedSite.ToposHom.comp (etaleRingedToposHom f)
          (piToposHom G Y eY)).toTopos.pushforward.obj 𝒢 ≅
      (RingedSite.ToposHom.comp (piToposHom F X eX)
          (AlgebraicSpace.ringedToposHom (inducedHom eX eY f))).toTopos.pushforward.obj 𝒢 where
  hom := CategoryTheory.ObjectProperty.homMk (compareMorphismIsoPresheaf eX eY f α 𝒢).hom
  inv := CategoryTheory.ObjectProperty.homMk (compareMorphismIsoPresheaf eX eY f α 𝒢).inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The canonical Type-`u` identification `π_{G,*} f_* ≅ f_small,* π_{F,*}` of
direct images of ringed topoi. -/
def compareMorphismIso :
    (RingedSite.ToposHom.comp (etaleRingedToposHom f)
          (piToposHom G Y eY)).toTopos.pushforward ≅
      (RingedSite.ToposHom.comp (piToposHom F X eX)
          (AlgebraicSpace.ringedToposHom (inducedHom eX eY f))).toTopos.pushforward :=
  NatIso.ofComponents (fun 𝒢 => compareMorphismIso_obj eX eY f α 𝒢) sorry

/-- The commutative square of ringed topoi with edges `f`, `π_F`, `π_G`, and
`f_small`. -/
def compareMorphism :
    RingedSite.ToposHom.CommSquare
      (etaleRingedSite X) (etaleRingedSite Y)
      (AlgebraicSpace.ringedSite F) (AlgebraicSpace.ringedSite G) where
  upper := etaleRingedToposHom f
  left := piToposHom F X eX
  right := piToposHom G Y eY
  lower := AlgebraicSpace.ringedToposHom (inducedHom eX eY f)
  cell :=
    { homIso := compareMorphismIso eX eY f α
      comm := sorry }

/-- The four edges of `compareMorphism` are `f`, `π_F`, `π_G`, and `f_small`, and
the stored `2`-cell is `compareMorphismIso`. -/
theorem compareMorphism_spec :
    (compareMorphism eX eY f α).upper = etaleRingedToposHom f ∧
      (compareMorphism eX eY f α).left = piToposHom F X eX ∧
      (compareMorphism eX eY f α).right = piToposHom G Y eY ∧
      (compareMorphism eX eY f α).lower =
        AlgebraicSpace.ringedToposHom (inducedHom eX eY f) ∧
      (compareMorphism eX eY f α).cell.homIso = compareMorphismIso eX eY f α :=
  sorry

end AlgebraicGeometry.GroupoidsOver
