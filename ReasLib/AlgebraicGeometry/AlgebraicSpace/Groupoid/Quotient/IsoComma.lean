module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.IsoComma
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Functoriality
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Atlas
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StackInSets
public import ReasLib.CategoryTheory.Category.ULift
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Postcomposition
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Hom.Equivalence

/-!
# 2-commutative square of the iso-comma groupoid

A morphism `f : Hom G H` determines cartesian functors `[g]`, `[f]`, `[U''/R''] ⟶ 𝒮_{U'}`,
and `𝒮_{U'} ⟶ [U'/R']` over `(Sch/S)_fppf`. The invertible `2`-cell has fibre the inverse of
the `R'`-factor of a `U''`-point.
-/

-- Public concrete constructions use private implementation maps and Prop-valued laws.
set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupoidAlgebraicSpace CategoryTheory.Limits Opposite
open CategoryTheory.CategoryOfElements CategoryTheory.Bicategory
open Functor.IsFibered.InGroupoids.Stackification
open CategoryTheory.Pseudofunctor.CoGrothendieck
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace.Hom

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}

private def isoCommaToTargetPreFunctorObj (f : Hom G H)
    (x : (preQuotient (isoComma f)).total) : (stackInSets H.U.left).total :=
  op ⟨op x.base, yonedaEquiv (x.fiber ≫ (isoCommaToTargetObject f).left)⟩

private theorem isoCommaToTargetPreFunctor_map_condition (f : Hom G H)
    {x y : (preQuotient (isoComma f)).total} (g : x ⟶ y) :
    H.U.left.functorOfPoints.map g.base.op
      (yonedaEquiv (y.fiber ≫ (isoCommaToTargetObject f).left)) =
        yonedaEquiv (x.fiber ≫ (isoCommaToTargetObject f).left) := sorry

private def isoCommaToTargetPreFunctorMap (f : Hom G H)
    {x y : (preQuotient (isoComma f)).total} (g : x ⟶ y) :
    isoCommaToTargetPreFunctorObj f x ⟶ isoCommaToTargetPreFunctorObj f y :=
  (homMk ⟨op y.base, yonedaEquiv (y.fiber ≫ (isoCommaToTargetObject f).left)⟩
    ⟨op x.base, yonedaEquiv (x.fiber ≫ (isoCommaToTargetObject f).left)⟩ g.base.op
    (isoCommaToTargetPreFunctor_map_condition f g)).op

private theorem isoCommaToTargetPreFunctor_laws (f : Hom G H) :
    (∀ x : (preQuotient (isoComma f)).total,
      isoCommaToTargetPreFunctorMap f (𝟙 x) = 𝟙 (isoCommaToTargetPreFunctorObj f x)) ∧
    (∀ (x y z : (preQuotient (isoComma f)).total) (g : x ⟶ y) (h : y ⟶ z),
      isoCommaToTargetPreFunctorMap f (g ≫ h) =
        isoCommaToTargetPreFunctorMap f g ≫ isoCommaToTargetPreFunctorMap f h) := sorry

private def isoCommaToTargetPreFunctor (f : Hom G H) :
    (preQuotient (isoComma f)).total ⥤ (stackInSets H.U.left).total where
  obj := isoCommaToTargetPreFunctorObj f
  map := isoCommaToTargetPreFunctorMap f
  map_id := (isoCommaToTargetPreFunctor_laws f).1
  map_comp := fun g h ↦ (isoCommaToTargetPreFunctor_laws f).2 _ _ _ g h

private theorem isoCommaToTargetPreFunctor_over (f : Hom G H) :
    isoCommaToTargetPreFunctor f ⋙ (stackInSets H.U.left).p =
      (preQuotient (isoComma f)).p := sorry

/-- The structure map to the target object space induces a cartesian functor on point prestacks. -/
def isoCommaToTargetPre (f : Hom G H) :
    CartesianBasedFunctor (preQuotient (isoComma f)).p (stackInSets H.U.left).p :=
  CartesianBasedFunctor.ofTargetInGroupoids
    (BasedFunctor.ofFunctor (isoCommaToTargetPreFunctor f) (isoCommaToTargetPreFunctor_over f))

/-- The selected stackification lift of `[U''/_p R''] ⟶ 𝒮_{U'}` through `[U''/_p R''] ⟶ [U''/R'']`. -/
private def isoCommaToTargetLift (f : Hom G H) :
    CartesianBasedFunctor.IsStackification.LiftChoice
      (i := (fppfQuotientStackPresentation (isoComma f)).comparison)
      (isoCommaToTargetPre f) :=
  CartesianBasedFunctor.IsStackification.liftChoice
    (fppfQuotientStackPresentation (isoComma f)).isStackification (isoCommaToTargetPre f)

/-- The cartesian `1`-morphism `[U''/R''] ⟶ 𝒮_{U'}` obtained by lifting the prestack map. -/
def isoCommaToTarget (f : Hom G H) :
    CartesianBasedFunctor (fppfQuotientStack (isoComma f)).p (stackInSets H.U.left).p :=
  (isoCommaToTargetLift f).lift

/-- The `R'`-factor of a prestack point of `U''`. -/
def isoCommaSpacePointFactor (f : Hom G H)
    (x : (preQuotient (isoComma f)).total) :
    ofOver x.base ⟶ H.R.left :=
  x.fiber ≫ (pullback.snd f.obj H.t).left

private theorem isoCommaPreHom_endpoints (f : Hom G H)
    (x : (preQuotient (isoComma f)).total) :
    (isoCommaSpacePointFactor f x ≫ H.i.left) ≫ H.s.left = (((prestackMap (isoCommaHom f)).comp (prestackMap f)).toFunctor.obj x).fiber ∧
    (isoCommaSpacePointFactor f x ≫ H.i.left) ≫ H.t.left =
      (H.points.map (op (𝟙 (((prestackMap (isoCommaHom f)).comp (prestackMap f)).toFunctor.obj x).base))).obj
        (((isoCommaToTargetPre f).comp (atlasToPreQuotient H)).toFunctor.obj x).fiber := sorry

/-- The fibre morphism of `[U'/_p R']` associated to the inverse of the `R'`-factor. -/
def isoCommaPreHom (f : Hom G H) (x : (preQuotient (isoComma f)).total) :
    ((prestackMap (isoCommaHom f)).comp (prestackMap f)).toFunctor.obj x ⟶
      ((isoCommaToTargetPre f).comp (atlasToPreQuotient H)).toFunctor.obj x where
  base := 𝟙 ((((prestackMap (isoCommaHom f)).comp (prestackMap f)).toFunctor.obj x).base)
  fiber :=
    SpacePointHom.ofArrow (isoCommaSpacePointFactor f x ≫ H.i.left) (isoCommaPreHom_endpoints f x).1 (isoCommaPreHom_endpoints f x).2

private theorem isoCommaPreInvHom_endpoints (f : Hom G H)
    (x : (preQuotient (isoComma f)).total) :
    (isoCommaSpacePointFactor f x) ≫ H.s.left = (((isoCommaToTargetPre f).comp (atlasToPreQuotient H)).toFunctor.obj x).fiber ∧
    (isoCommaSpacePointFactor f x) ≫ H.t.left =
      (H.points.map (op (𝟙 (((isoCommaToTargetPre f).comp (atlasToPreQuotient H)).toFunctor.obj x).base))).obj
        (((prestackMap (isoCommaHom f)).comp (prestackMap f)).toFunctor.obj x).fiber := sorry

/-- The inverse fibre morphism, whose underlying arrow is the `R'`-factor itself. -/
def isoCommaPreInvHom (f : Hom G H) (x : (preQuotient (isoComma f)).total) :
    ((isoCommaToTargetPre f).comp (atlasToPreQuotient H)).toFunctor.obj x ⟶
      ((prestackMap (isoCommaHom f)).comp (prestackMap f)).toFunctor.obj x where
  base := 𝟙 ((((isoCommaToTargetPre f).comp (atlasToPreQuotient H)).toFunctor.obj x).base)
  fiber := SpacePointHom.ofArrow (isoCommaSpacePointFactor f x) (isoCommaPreInvHom_endpoints f x).1 (isoCommaPreInvHom_endpoints f x).2

private def comparisonLaws {X Y C : Type _} [Category X] [Category Y] [Category C]
    (p : X ⥤ C) (q : Y ⥤ C) (F K : CartesianBasedFunctor p q)
    (homApp : ∀ x : X, F.toFunctor.obj x ⟶ K.toFunctor.obj x)
    (invApp : ∀ x : X, K.toFunctor.obj x ⟶ F.toFunctor.obj x) : Prop :=
  (∀ ⦃x y : X⦄ (g : x ⟶ y),
      F.toFunctor.map g ≫ homApp y = homApp x ≫ K.toFunctor.map g) ∧
    (∀ x : X,
      q.IsHomLift (𝟙 (p.obj x)) (homApp x)) ∧
    (∀ ⦃x y : X⦄ (g : x ⟶ y),
      K.toFunctor.map g ≫ invApp y = invApp x ≫ F.toFunctor.map g) ∧
    (∀ x : X,
      q.IsHomLift (𝟙 (p.obj x)) (invApp x)) ∧
    (∀ x : X, homApp x ≫ invApp x = 𝟙 (F.toFunctor.obj x)) ∧
    (∀ x : X, invApp x ≫ homApp x = 𝟙 (K.toFunctor.obj x))

private theorem isoCommaPreIso_laws (f : Hom G H) :
    let F := (prestackMap (isoCommaHom f)).comp (prestackMap f)
    let K := (isoCommaToTargetPre f).comp (atlasToPreQuotient H)
    let homApp : ∀ x : (preQuotient (isoComma f)).total, F.toFunctor.obj x ⟶ K.toFunctor.obj x :=
      fun x ↦ isoCommaPreHom f x
    let invApp : ∀ x : (preQuotient (isoComma f)).total, K.toFunctor.obj x ⟶ F.toFunctor.obj x :=
      fun x ↦ isoCommaPreInvHom f x
    comparisonLaws (preQuotient (isoComma f)).p (preQuotient H).p F K homApp invApp := sorry

/-- The prestack `2`-isomorphism `[g]_p ≫ [f]_p ≅ toTarget_p ≫ atlas_p`. -/
def isoCommaPreIso (f : Hom G H) :
    (prestackMap (isoCommaHom f)).comp (prestackMap f) ≅
      (isoCommaToTargetPre f).comp (atlasToPreQuotient H) :=
  let build {X Y C : Type _} [Category X] [Category Y] [Category C]
      (p : X ⥤ C) (q : Y ⥤ C) (F K : CartesianBasedFunctor p q)
      (homApp : ∀ x : X, F.toFunctor.obj x ⟶ K.toFunctor.obj x)
      (invApp : ∀ x : X, K.toFunctor.obj x ⟶ F.toFunctor.obj x)
      (laws : comparisonLaws p q F K homApp invApp) : F ≅ K :=
    { hom :=
        CartesianBasedFunctor.homMk (F := F) (G := K)
          { toNatTrans := { app := homApp, naturality := laws.1 }
            isHomLift' := laws.2.1 }
      inv :=
        CartesianBasedFunctor.homMk (F := K) (G := F)
          { toNatTrans := { app := invApp, naturality := laws.2.2.1 }
            isHomLift' := laws.2.2.2.1 }
      hom_inv_id := by
        apply ObjectProperty.hom_ext
        apply BasedNatTrans.ext
        apply NatTrans.ext
        funext x
        exact laws.2.2.2.2.1 x
      inv_hom_id := by
        apply ObjectProperty.hom_ext
        apply BasedNatTrans.ext
        apply NatTrans.ext
        funext x
        exact laws.2.2.2.2.2 x }
  let F := (prestackMap (isoCommaHom f)).comp (prestackMap f)
  let K := (isoCommaToTargetPre f).comp (atlasToPreQuotient H)
  let homApp : ∀ x : (preQuotient (isoComma f)).total, F.toFunctor.obj x ⟶ K.toFunctor.obj x :=
      fun x ↦ isoCommaPreHom f x
  let invApp : ∀ x : (preQuotient (isoComma f)).total, K.toFunctor.obj x ⟶ F.toFunctor.obj x :=
      fun x ↦ isoCommaPreInvHom f x
  build (preQuotient (isoComma f)).p (preQuotient H).p F K homApp invApp (isoCommaPreIso_laws f)

private theorem isoCommaPreStackIso_laws (f : Hom G H) :
    let F := (prestackMap (isoCommaHom f)).comp (prestackToQuotient f)
    let K := (isoCommaToTargetPre f).comp (fppfAtlas H)
    let homApp : ∀ x : (preQuotient (isoComma f)).total, F.toFunctor.obj x ⟶ K.toFunctor.obj x :=
      fun x ↦
          (fppfQuotientStackPresentation H).comparison.toFunctor.map (isoCommaPreHom f x)
    let invApp : ∀ x : (preQuotient (isoComma f)).total, K.toFunctor.obj x ⟶ F.toFunctor.obj x :=
      fun x ↦
          (fppfQuotientStackPresentation H).comparison.toFunctor.map (isoCommaPreInvHom f x)
    comparisonLaws (preQuotient (isoComma f)).p (fppfQuotientStack H).p F K homApp invApp := sorry

/-- The stacked `2`-isomorphism obtained by applying stackification of `[U'/R']` to the
prestack components of `isoCommaPreIso`. -/
private def isoCommaPreStackIso (f : Hom G H) :
    (prestackMap (isoCommaHom f)).comp (prestackToQuotient f) ≅
      (isoCommaToTargetPre f).comp (fppfAtlas H) :=
  let build {X Y C : Type _} [Category X] [Category Y] [Category C]
      (p : X ⥤ C) (q : Y ⥤ C) (F K : CartesianBasedFunctor p q)
      (homApp : ∀ x : X, F.toFunctor.obj x ⟶ K.toFunctor.obj x)
      (invApp : ∀ x : X, K.toFunctor.obj x ⟶ F.toFunctor.obj x)
      (laws : comparisonLaws p q F K homApp invApp) : F ≅ K :=
    { hom :=
        CartesianBasedFunctor.homMk (F := F) (G := K)
          { toNatTrans := { app := homApp, naturality := laws.1 }
            isHomLift' := laws.2.1 }
      inv :=
        CartesianBasedFunctor.homMk (F := K) (G := F)
          { toNatTrans := { app := invApp, naturality := laws.2.2.1 }
            isHomLift' := laws.2.2.2.1 }
      hom_inv_id := by
        apply ObjectProperty.hom_ext
        apply BasedNatTrans.ext
        apply NatTrans.ext
        funext x
        exact laws.2.2.2.2.1 x
      inv_hom_id := by
        apply ObjectProperty.hom_ext
        apply BasedNatTrans.ext
        apply NatTrans.ext
        funext x
        exact laws.2.2.2.2.2 x }
  let F := (prestackMap (isoCommaHom f)).comp (prestackToQuotient f)
  let K := (isoCommaToTargetPre f).comp (fppfAtlas H)
  let homApp : ∀ x : (preQuotient (isoComma f)).total, F.toFunctor.obj x ⟶ K.toFunctor.obj x :=
      fun x ↦
          (fppfQuotientStackPresentation H).comparison.toFunctor.map (isoCommaPreHom f x)
  let invApp : ∀ x : (preQuotient (isoComma f)).total, K.toFunctor.obj x ⟶ F.toFunctor.obj x :=
      fun x ↦
          (fppfQuotientStackPresentation H).comparison.toFunctor.map (isoCommaPreInvHom f x)
  build (preQuotient (isoComma f)).p (fppfQuotientStack H).p F K homApp invApp (isoCommaPreStackIso_laws f)

private theorem isoCommaLeftAssoc_laws (f : Hom G H) :
    let F := ((fppfQuotientStackPresentation (isoComma f)).comparison.comp
        (quotientStackMap (isoCommaHom f))).comp (quotientStackMap f)
    let K := (fppfQuotientStackPresentation (isoComma f)).comparison.comp
        ((quotientStackMap (isoCommaHom f)).comp (quotientStackMap f))
    let homApp : ∀ x : (preQuotient (isoComma f)).total, F.toFunctor.obj x ⟶ K.toFunctor.obj x :=
      fun (x : (preQuotient (isoComma f)).total) ↦
          𝟙 ((((fppfQuotientStackPresentation (isoComma f)).comparison.comp
              (quotientStackMap (isoCommaHom f))).comp (quotientStackMap f)).toFunctor.obj x)
    let invApp : ∀ x : (preQuotient (isoComma f)).total, K.toFunctor.obj x ⟶ F.toFunctor.obj x :=
      fun (x : (preQuotient (isoComma f)).total) ↦
          𝟙 ((((fppfQuotientStackPresentation (isoComma f)).comparison.comp
              (quotientStackMap (isoCommaHom f))).comp (quotientStackMap f)).toFunctor.obj x)
    comparisonLaws (preQuotient (isoComma f)).p (fppfQuotientStack H).p F K homApp invApp := sorry

/-- Identity-on-objects associator identifying `((i ≫ [g]) ≫ [f])` with `i ≫ ([g] ≫ [f])`. -/
private def isoCommaLeftAssoc (f : Hom G H) :
    ((fppfQuotientStackPresentation (isoComma f)).comparison.comp
        (quotientStackMap (isoCommaHom f))).comp (quotientStackMap f) ≅
      (fppfQuotientStackPresentation (isoComma f)).comparison.comp
        ((quotientStackMap (isoCommaHom f)).comp (quotientStackMap f)) :=
  let build {X Y C : Type _} [Category X] [Category Y] [Category C]
      (p : X ⥤ C) (q : Y ⥤ C) (F K : CartesianBasedFunctor p q)
      (homApp : ∀ x : X, F.toFunctor.obj x ⟶ K.toFunctor.obj x)
      (invApp : ∀ x : X, K.toFunctor.obj x ⟶ F.toFunctor.obj x)
      (laws : comparisonLaws p q F K homApp invApp) : F ≅ K :=
    { hom :=
        CartesianBasedFunctor.homMk (F := F) (G := K)
          { toNatTrans := { app := homApp, naturality := laws.1 }
            isHomLift' := laws.2.1 }
      inv :=
        CartesianBasedFunctor.homMk (F := K) (G := F)
          { toNatTrans := { app := invApp, naturality := laws.2.2.1 }
            isHomLift' := laws.2.2.2.1 }
      hom_inv_id := by
        apply ObjectProperty.hom_ext
        apply BasedNatTrans.ext
        apply NatTrans.ext
        funext x
        exact laws.2.2.2.2.1 x
      inv_hom_id := by
        apply ObjectProperty.hom_ext
        apply BasedNatTrans.ext
        apply NatTrans.ext
        funext x
        exact laws.2.2.2.2.2 x }
  let F := ((fppfQuotientStackPresentation (isoComma f)).comparison.comp
        (quotientStackMap (isoCommaHom f))).comp (quotientStackMap f)
  let K := (fppfQuotientStackPresentation (isoComma f)).comparison.comp
        ((quotientStackMap (isoCommaHom f)).comp (quotientStackMap f))
  let homApp : ∀ x : (preQuotient (isoComma f)).total, F.toFunctor.obj x ⟶ K.toFunctor.obj x :=
      fun (x : (preQuotient (isoComma f)).total) ↦
          𝟙 ((((fppfQuotientStackPresentation (isoComma f)).comparison.comp
              (quotientStackMap (isoCommaHom f))).comp (quotientStackMap f)).toFunctor.obj x)
  let invApp : ∀ x : (preQuotient (isoComma f)).total, K.toFunctor.obj x ⟶ F.toFunctor.obj x :=
      fun (x : (preQuotient (isoComma f)).total) ↦
          𝟙 ((((fppfQuotientStackPresentation (isoComma f)).comparison.comp
              (quotientStackMap (isoCommaHom f))).comp (quotientStackMap f)).toFunctor.obj x)
  build (preQuotient (isoComma f)).p (fppfQuotientStack H).p F K homApp invApp (isoCommaLeftAssoc_laws f)

private theorem isoCommaLeftPreAssoc_laws (f : Hom G H) :
    let F := (prestackToQuotient (isoCommaHom f)).comp (quotientStackMap f)
    let K := (prestackMap (isoCommaHom f)).comp
        ((fppfQuotientStackPresentation G).comparison.comp (quotientStackMap f))
    let homApp : ∀ x : (preQuotient (isoComma f)).total, F.toFunctor.obj x ⟶ K.toFunctor.obj x :=
      fun (x : (preQuotient (isoComma f)).total) ↦
          𝟙 (((prestackToQuotient (isoCommaHom f)).comp (quotientStackMap f)).toFunctor.obj x)
    let invApp : ∀ x : (preQuotient (isoComma f)).total, K.toFunctor.obj x ⟶ F.toFunctor.obj x :=
      fun (x : (preQuotient (isoComma f)).total) ↦
          𝟙 (((prestackToQuotient (isoCommaHom f)).comp (quotientStackMap f)).toFunctor.obj x)
    comparisonLaws (preQuotient (isoComma f)).p (fppfQuotientStack H).p F K homApp invApp := sorry

/-- Identity-on-objects associator identifying `(prestackToQuotient g) ≫ [f]` with
`[g]_p ≫ ((i_G) ≫ [f])`. -/
private def isoCommaLeftPreAssoc (f : Hom G H) :
    (prestackToQuotient (isoCommaHom f)).comp (quotientStackMap f) ≅
      (prestackMap (isoCommaHom f)).comp
        ((fppfQuotientStackPresentation G).comparison.comp (quotientStackMap f)) :=
  let build {X Y C : Type _} [Category X] [Category Y] [Category C]
      (p : X ⥤ C) (q : Y ⥤ C) (F K : CartesianBasedFunctor p q)
      (homApp : ∀ x : X, F.toFunctor.obj x ⟶ K.toFunctor.obj x)
      (invApp : ∀ x : X, K.toFunctor.obj x ⟶ F.toFunctor.obj x)
      (laws : comparisonLaws p q F K homApp invApp) : F ≅ K :=
    { hom :=
        CartesianBasedFunctor.homMk (F := F) (G := K)
          { toNatTrans := { app := homApp, naturality := laws.1 }
            isHomLift' := laws.2.1 }
      inv :=
        CartesianBasedFunctor.homMk (F := K) (G := F)
          { toNatTrans := { app := invApp, naturality := laws.2.2.1 }
            isHomLift' := laws.2.2.2.1 }
      hom_inv_id := by
        apply ObjectProperty.hom_ext
        apply BasedNatTrans.ext
        apply NatTrans.ext
        funext x
        exact laws.2.2.2.2.1 x
      inv_hom_id := by
        apply ObjectProperty.hom_ext
        apply BasedNatTrans.ext
        apply NatTrans.ext
        funext x
        exact laws.2.2.2.2.2 x }
  let F := (prestackToQuotient (isoCommaHom f)).comp (quotientStackMap f)
  let K := (prestackMap (isoCommaHom f)).comp
        ((fppfQuotientStackPresentation G).comparison.comp (quotientStackMap f))
  let homApp : ∀ x : (preQuotient (isoComma f)).total, F.toFunctor.obj x ⟶ K.toFunctor.obj x :=
      fun (x : (preQuotient (isoComma f)).total) ↦
          𝟙 (((prestackToQuotient (isoCommaHom f)).comp (quotientStackMap f)).toFunctor.obj x)
  let invApp : ∀ x : (preQuotient (isoComma f)).total, K.toFunctor.obj x ⟶ F.toFunctor.obj x :=
      fun (x : (preQuotient (isoComma f)).total) ↦
          𝟙 (((prestackToQuotient (isoCommaHom f)).comp (quotientStackMap f)).toFunctor.obj x)
  build (preQuotient (isoComma f)).p (fppfQuotientStack H).p F K homApp invApp (isoCommaLeftPreAssoc_laws f)

private theorem isoCommaRightAssoc_laws (f : Hom G H) :
    let F := ((fppfQuotientStackPresentation (isoComma f)).comparison.comp
        (isoCommaToTarget f)).comp (fppfAtlas H)
    let K := (fppfQuotientStackPresentation (isoComma f)).comparison.comp
        ((isoCommaToTarget f).comp (fppfAtlas H))
    let homApp : ∀ x : (preQuotient (isoComma f)).total, F.toFunctor.obj x ⟶ K.toFunctor.obj x :=
      fun (x : (preQuotient (isoComma f)).total) ↦
          𝟙 ((((fppfQuotientStackPresentation (isoComma f)).comparison.comp
              (isoCommaToTarget f)).comp (fppfAtlas H)).toFunctor.obj x)
    let invApp : ∀ x : (preQuotient (isoComma f)).total, K.toFunctor.obj x ⟶ F.toFunctor.obj x :=
      fun (x : (preQuotient (isoComma f)).total) ↦
          𝟙 ((((fppfQuotientStackPresentation (isoComma f)).comparison.comp
              (isoCommaToTarget f)).comp (fppfAtlas H)).toFunctor.obj x)
    comparisonLaws (preQuotient (isoComma f)).p (fppfQuotientStack H).p F K homApp invApp := sorry

/-- Identity-on-objects associator identifying `((i ≫ toTarget) ≫ atlas)` with
`i ≫ (toTarget ≫ atlas)`. -/
private def isoCommaRightAssoc (f : Hom G H) :
    ((fppfQuotientStackPresentation (isoComma f)).comparison.comp
        (isoCommaToTarget f)).comp (fppfAtlas H) ≅
      (fppfQuotientStackPresentation (isoComma f)).comparison.comp
        ((isoCommaToTarget f).comp (fppfAtlas H)) :=
  let build {X Y C : Type _} [Category X] [Category Y] [Category C]
      (p : X ⥤ C) (q : Y ⥤ C) (F K : CartesianBasedFunctor p q)
      (homApp : ∀ x : X, F.toFunctor.obj x ⟶ K.toFunctor.obj x)
      (invApp : ∀ x : X, K.toFunctor.obj x ⟶ F.toFunctor.obj x)
      (laws : comparisonLaws p q F K homApp invApp) : F ≅ K :=
    { hom :=
        CartesianBasedFunctor.homMk (F := F) (G := K)
          { toNatTrans := { app := homApp, naturality := laws.1 }
            isHomLift' := laws.2.1 }
      inv :=
        CartesianBasedFunctor.homMk (F := K) (G := F)
          { toNatTrans := { app := invApp, naturality := laws.2.2.1 }
            isHomLift' := laws.2.2.2.1 }
      hom_inv_id := by
        apply ObjectProperty.hom_ext
        apply BasedNatTrans.ext
        apply NatTrans.ext
        funext x
        exact laws.2.2.2.2.1 x
      inv_hom_id := by
        apply ObjectProperty.hom_ext
        apply BasedNatTrans.ext
        apply NatTrans.ext
        funext x
        exact laws.2.2.2.2.2 x }
  let F := ((fppfQuotientStackPresentation (isoComma f)).comparison.comp
        (isoCommaToTarget f)).comp (fppfAtlas H)
  let K := (fppfQuotientStackPresentation (isoComma f)).comparison.comp
        ((isoCommaToTarget f).comp (fppfAtlas H))
  let homApp : ∀ x : (preQuotient (isoComma f)).total, F.toFunctor.obj x ⟶ K.toFunctor.obj x :=
      fun (x : (preQuotient (isoComma f)).total) ↦
          𝟙 ((((fppfQuotientStackPresentation (isoComma f)).comparison.comp
              (isoCommaToTarget f)).comp (fppfAtlas H)).toFunctor.obj x)
  let invApp : ∀ x : (preQuotient (isoComma f)).total, K.toFunctor.obj x ⟶ F.toFunctor.obj x :=
      fun (x : (preQuotient (isoComma f)).total) ↦
          𝟙 ((((fppfQuotientStackPresentation (isoComma f)).comparison.comp
              (isoCommaToTarget f)).comp (fppfAtlas H)).toFunctor.obj x)
  build (preQuotient (isoComma f)).p (fppfQuotientStack H).p F K homApp invApp (isoCommaRightAssoc_laws f)

/-- The stackification lift of `[g]_p ≫ [f]_p` whose lift is `[g] ≫ [f]`. -/
private def isoCommaLeftLift (f : Hom G H) :
    CartesianBasedFunctor.IsStackification.LiftChoice
      (i := (fppfQuotientStackPresentation (isoComma f)).comparison)
      ((isoCommaToTargetPre f).comp (fppfAtlas H)) where
  lift := (quotientStackMap (isoCommaHom f)).comp (quotientStackMap f)
  comparison :=
    (isoCommaLeftAssoc f).symm ≪≫
      (CartesianBasedFunctor.postcomp (preQuotient (isoComma f)).p
          (quotientStackMap f)).mapIso (quotientStackMap_comp (isoCommaHom f)) ≪≫
      isoCommaLeftPreAssoc f ≪≫
      (CartesianBasedFunctor.precomp (fppfQuotientStack H).p
          (prestackMap (isoCommaHom f))).mapIso (quotientStackMap_comp f) ≪≫
      isoCommaPreStackIso f

/-- The stackification lift of `toTarget_p ≫ atlas` whose lift is `toTarget ≫ atlas`. -/
private def isoCommaRightLift (f : Hom G H) :
    CartesianBasedFunctor.IsStackification.LiftChoice
      (i := (fppfQuotientStackPresentation (isoComma f)).comparison)
      ((isoCommaToTargetPre f).comp (fppfAtlas H)) where
  lift := (isoCommaToTarget f).comp (fppfAtlas H)
  comparison :=
    (isoCommaRightAssoc f).symm ≪≫
      (CartesianBasedFunctor.postcomp (preQuotient (isoComma f)).p (fppfAtlas H)).mapIso
        (isoCommaToTargetLift f).comparison

/-- The stacked `2`-isomorphism `[g] ≫ [f] ≅ toTarget ≫ atlas`. -/
def isoCommaIso (f : Hom G H) :
    (quotientStackMap (isoCommaHom f)).comp (quotientStackMap f) ≅
      (isoCommaToTarget f).comp (fppfAtlas H) :=
  CartesianBasedFunctor.IsStackification.LiftChoice.comparisonIso
    (fppfQuotientStackPresentation (isoComma f)).isStackification
    (isoCommaLeftLift f) (isoCommaRightLift f)

/-- The cartesian `1`-morphism `[U''/R''] ⟶ 𝒮_{U'}` after aligning `𝒮_{U'}` to the Hom-universe
of `[U'/R']`. -/
def isoCommaToTargetULift (f : Hom G H) :
    CartesianBasedFunctor (fppfQuotientStack (isoComma f)).p (stackInSetsULift H.U.left).p :=
  (isoCommaToTarget f).comp (stackInSetsULift.up H.U.left)

/-- `isoCommaToTargetULift` is `isoCommaToTarget` followed by the morphism-universe lift. -/
theorem isoCommaToTargetULift_eq (f : Hom G H) :
    isoCommaToTargetULift f =
      (isoCommaToTarget f).comp (stackInSetsULift.up H.U.left) := rfl

private theorem isoCommaAlignedAssoc_laws (f : Hom G H) :
    let F := (isoCommaToTarget f).comp (fppfAtlas H)
    let K := (isoCommaToTargetULift f).comp (fppfAtlasULift H)
    let homApp : ∀ x : (fppfQuotientStack (isoComma f)).total, F.toFunctor.obj x ⟶ K.toFunctor.obj x :=
      fun (x : (fppfQuotientStack (isoComma f)).total) ↦
          (fppfAtlas H).toFunctor.map
            ((Cat.TwoULift.equiv.{u + 1, u, u + 1, u + 1}
                (stackInSets H.U.left).total).unitIso.hom.app
              ((isoCommaToTarget f).toFunctor.obj x))
    let invApp : ∀ x : (fppfQuotientStack (isoComma f)).total, K.toFunctor.obj x ⟶ F.toFunctor.obj x :=
      fun (x : (fppfQuotientStack (isoComma f)).total) ↦
          (fppfAtlas H).toFunctor.map
            ((Cat.TwoULift.equiv.{u + 1, u, u + 1, u + 1}
                (stackInSets H.U.left).total).unitIso.inv.app
              ((isoCommaToTarget f).toFunctor.obj x))
    comparisonLaws (fppfQuotientStack (isoComma f)).p (fppfQuotientStack H).p F K homApp invApp := sorry

/-- Comparison identifying `toTarget ≫ atlas` with the universe-aligned composite into `𝒮_{U'}`,
using the unit of the two-universe equivalence of `𝒮_{U'}`. -/
private def isoCommaAlignedAssoc (f : Hom G H) :
    (isoCommaToTarget f).comp (fppfAtlas H) ≅
      (isoCommaToTargetULift f).comp (fppfAtlasULift H) :=
  let build {X Y C : Type _} [Category X] [Category Y] [Category C]
      (p : X ⥤ C) (q : Y ⥤ C) (F K : CartesianBasedFunctor p q)
      (homApp : ∀ x : X, F.toFunctor.obj x ⟶ K.toFunctor.obj x)
      (invApp : ∀ x : X, K.toFunctor.obj x ⟶ F.toFunctor.obj x)
      (laws : comparisonLaws p q F K homApp invApp) : F ≅ K :=
    { hom :=
        CartesianBasedFunctor.homMk (F := F) (G := K)
          { toNatTrans := { app := homApp, naturality := laws.1 }
            isHomLift' := laws.2.1 }
      inv :=
        CartesianBasedFunctor.homMk (F := K) (G := F)
          { toNatTrans := { app := invApp, naturality := laws.2.2.1 }
            isHomLift' := laws.2.2.2.1 }
      hom_inv_id := by
        apply ObjectProperty.hom_ext
        apply BasedNatTrans.ext
        apply NatTrans.ext
        funext x
        exact laws.2.2.2.2.1 x
      inv_hom_id := by
        apply ObjectProperty.hom_ext
        apply BasedNatTrans.ext
        apply NatTrans.ext
        funext x
        exact laws.2.2.2.2.2 x }
  let F := (isoCommaToTarget f).comp (fppfAtlas H)
  let K := (isoCommaToTargetULift f).comp (fppfAtlasULift H)
  let homApp : ∀ x : (fppfQuotientStack (isoComma f)).total, F.toFunctor.obj x ⟶ K.toFunctor.obj x :=
      fun (x : (fppfQuotientStack (isoComma f)).total) ↦
          (fppfAtlas H).toFunctor.map
            ((Cat.TwoULift.equiv.{u + 1, u, u + 1, u + 1}
                (stackInSets H.U.left).total).unitIso.hom.app
              ((isoCommaToTarget f).toFunctor.obj x))
  let invApp : ∀ x : (fppfQuotientStack (isoComma f)).total, K.toFunctor.obj x ⟶ F.toFunctor.obj x :=
      fun (x : (fppfQuotientStack (isoComma f)).total) ↦
          (fppfAtlas H).toFunctor.map
            ((Cat.TwoULift.equiv.{u + 1, u, u + 1, u + 1}
                (stackInSets H.U.left).total).unitIso.inv.app
              ((isoCommaToTarget f).toFunctor.obj x))
  build (fppfQuotientStack (isoComma f)).p (fppfQuotientStack H).p F K homApp invApp (isoCommaAlignedAssoc_laws f)

/-- The stacked `2`-isomorphism `[g] ≫ [f] ≅ left ≫ fppfAtlas` after aligning `𝒮_{U'}`. -/
def isoCommaIsoULift (f : Hom G H) :
    (quotientStackMap (isoCommaHom f)).comp (quotientStackMap f) ≅
      (isoCommaToTargetULift f).comp (fppfAtlasULift H) :=
  isoCommaIso f ≪≫ isoCommaAlignedAssoc f

/-- The fibre of the prestack cell at a `U''`-point is the inverse of the `R'`-factor. -/
theorem isoCommaIso_hom_app (f : Hom G H) (x : (preQuotient (isoComma f)).total) :
    (isoCommaPreHom f x).fiber.arrow = isoCommaSpacePointFactor f x ≫ H.i.left := rfl

/-- The right leg `[f] : [U/R] ⟶ [U'/R']` as a morphism of stacks in groupoids. -/
def isoCommaConeRight (f : Hom G H) :
    fppfQuotientStack G ⟶ fppfQuotientStack H :=
  StackOver.Groupoids.Hom.lift
    (FiberedCategoryOver.Groupoids.ofBasedFunctor (quotientStackMap f).toBasedFunctor)

/-- The first projection `[g] : [U''/R''] ⟶ [U/R]` as a morphism of stacks in groupoids. -/
def isoCommaConeFst (f : Hom G H) :
    fppfQuotientStack (isoComma f) ⟶ fppfQuotientStack G :=
  StackOver.Groupoids.Hom.lift
    (FiberedCategoryOver.Groupoids.ofBasedFunctor
      (quotientStackMap (isoCommaHom f)).toBasedFunctor)

/-- The left leg `[U''/R''] ⟶ 𝒮_{U'}` of the iso-comma square, after aligning `𝒮_{U'}` to the
Hom-universe of `[U'/R']`. -/
def isoCommaConeSnd (f : Hom G H) :
    fppfQuotientStack (isoComma f) ⟶ stackInSetsULift H.U.left :=
  StackOver.Groupoids.Hom.lift
    (FiberedCategoryOver.Groupoids.ofBasedFunctor
      (isoCommaToTargetULift f).toBasedFunctor)

/-- The bottom atlas `𝒮_{U'} ⟶ [U'/R']` of the iso-comma square, after aligning `𝒮_{U'}`. -/
def isoCommaConeBottom (f : Hom G H) :
    stackInSetsULift H.U.left ⟶ fppfQuotientStack H :=
  StackOver.Groupoids.Hom.lift
    (FiberedCategoryOver.Groupoids.ofBasedFunctor (fppfAtlasULift H).toBasedFunctor)

/-- The packaged `2`-isomorphism `[g] ≫ [f] ≅ left ≫ fppfAtlas` of the iso-comma square. -/
def isoCommaConeIso (f : Hom G H) :
    isoCommaConeFst f ≫ isoCommaConeRight f ≅
      isoCommaConeSnd f ≫ isoCommaConeBottom f :=
  StackOver.Groupoids.Hom.isoMk
    (FiberedCategoryOver.Groupoids.BasedFunctorIso.lift
      (CartesianBasedFunctor.toBasedIso (isoCommaIsoULift f)))

/-- The `2`-commutative square with apex `[U''/R'']`, right leg `[f] : [U/R] ⟶ [U'/R']`,
left leg `[U''/R''] ⟶ 𝒮_{U'}`, and bottom atlas `𝒮_{U'} ⟶ [U'/R']`. -/
def isoCommaCone (f : Hom G H) :
    PseudoPullbackCone (isoCommaConeRight f) (isoCommaConeBottom f) where
  pt := fppfQuotientStack (isoComma f)
  fst := isoCommaConeFst f
  snd := isoCommaConeSnd f
  iso := isoCommaConeIso f

/-- The apex of `isoCommaCone f` is `[U''/R'']`. -/
theorem isoCommaCone_pt (f : Hom G H) :
    (isoCommaCone f).pt = fppfQuotientStack (isoComma f) := rfl

/-- The first projection of `isoCommaCone f` is `[g]`. -/
theorem isoCommaCone_fst (f : Hom G H) :
    (isoCommaCone f).fst = isoCommaConeFst f := rfl

/-- The second projection of `isoCommaCone f` is the left leg `[U''/R''] ⟶ 𝒮_{U'}`. -/
theorem isoCommaCone_snd (f : Hom G H) :
    (isoCommaCone f).snd = isoCommaConeSnd f := rfl

/-- The `2`-cell of `isoCommaCone f` is `isoCommaConeIso f`. -/
theorem isoCommaCone_iso (f : Hom G H) :
    (isoCommaCone f).iso = isoCommaConeIso f := rfl

/-- The quotient stack of the iso-comma groupoid is the two-fibre product of the induced
quotient-stack morphism and the target atlas. -/
theorem isoCommaCone_isBilimit (f : Hom G H) :
    (isoCommaCone f).IsBilimit := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace.Hom
