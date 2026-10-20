/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import ReasLib.Algebra.Category.CommAlgCat.IndEtale.Lift
public import ReasLib.Algebra.Category.CommAlgCat.IndEtale.Reindex
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.AffineIndEtaleAlgebra
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.Pullback

/-!
# Closed immersions and affine ind-étale sites

Pullback along a closed immersion of affine schemes has a fully faithful left
adjoint, constructed from the ind-étale algebra lift and spectra.
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty Opposite AlgebraicGeometry
noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.ProEt
variable {X Z : Scheme.{u}} [IsAffine X] [IsAffine Z]

/-- The kernel of the map on global sections induced by a closed immersion of
affine schemes. -/
def AffineIndEtale.ker {X Z : Scheme.{u}} [IsAffine X] [IsAffine Z]
    (i : Z ⟶ X) [IsClosedImmersion i] : Ideal Γ(X, ⊤) :=
  RingHom.ker i.appTop.hom

/-- A closed immersion of affines identifies `Γ(Z, ⊤)` with `Γ(X, ⊤) ⧸ ker i`. -/
def AffineIndEtale.quotientIso {X Z : Scheme.{u}} [IsAffine X] [IsAffine Z]
    (i : Z ⟶ X) [IsClosedImmersion i] :
    (Γ(X, ⊤) ⧸ ker i) ≃+* Γ(Z, ⊤) :=
  RingHom.quotientKerEquivOfSurjective
    (IsClosedImmersion.isAffine_surjective_of_isAffine i).2

/-- The quotient comparison sends the class of a global section to its image
in `Γ(Z, ⊤)`. -/
theorem AffineIndEtale.quotientIso_apply_mk {X Z : Scheme.{u}} [IsAffine X]
    [IsAffine Z] (i : Z ⟶ X) [IsClosedImmersion i] (a : Γ(X, ⊤)) :
    quotientIso i (Ideal.Quotient.mk (ker i) a) = i.appTop.hom a := rfl

/-- Pullback along a closed immersion of affines preserves affine ind-étale
objects of the small pro-étale site. -/
theorem AffineIndEtale.objects_map_baseChange (i : Z ⟶ X) [IsClosedImmersion i]
    (U : AffineIndEtale X) :
    affineIndEtaleObjects Z
      ((affineIndEtaleInclusion X ⋙ smallProetalePullback i).obj U) := sorry

/-- Base change of affine ind-étale objects along a closed immersion, sending
`U` to `U ×_X Z`. -/
def AffineIndEtale.baseChange (i : Z ⟶ X) [IsClosedImmersion i] :
    AffineIndEtale X ⥤ AffineIndEtale Z :=
  (affineIndEtaleObjects Z).lift (affineIndEtaleInclusion X ⋙ smallProetalePullback i)
    (objects_map_baseChange i)

/-- Affine ind-étale base change sits over pro-étale base change via the
inclusions. -/
def AffineIndEtale.baseChange_comp_inclusion (i : Z ⟶ X) [IsClosedImmersion i] :
    AffineIndEtale.baseChange i ⋙ affineIndEtaleInclusion Z ≅
      affineIndEtaleInclusion X ⋙ smallProetalePullback i :=
  (affineIndEtaleObjects Z).liftCompιIso
    (affineIndEtaleInclusion X ⋙ smallProetalePullback i)
    (objects_map_baseChange i)

/-- The underlying scheme of affine ind-étale base change is the fibre product
over `X`. -/
theorem AffineIndEtale.baseChange_obj (i : Z ⟶ X) [IsClosedImmersion i]
    (U : AffineIndEtale X) :
    ((AffineIndEtale.baseChange i).obj U).obj.left =
      Limits.pullback U.obj.hom i := rfl

/-- Affine ind-étale base change is continuous for the affine ind-étale
topologies. -/
instance AffineIndEtale.baseChange_isContinuous (i : Z ⟶ X)
    [IsClosedImmersion i] :
    Functor.IsContinuous (AffineIndEtale.baseChange i)
      (affineIndEtaleTopology X) (affineIndEtaleTopology Z) := sorry

/-- Transport of `CommAlgCat.IndEtale.lift` along `Γ(Z, ⊤) ≃ Γ(X, ⊤) ⧸ ker i`. -/
def AffineIndEtale.algebraLift (i : Z ⟶ X) [IsClosedImmersion i] :
    CommAlgCat.IndEtale.{u} Γ(Z, ⊤) ⥤ CommAlgCat.IndEtale.{u} Γ(X, ⊤) :=
  CommAlgCat.IndEtale.reindex (AffineIndEtale.quotientIso i).symm ⋙
    CommAlgCat.IndEtale.lift (AffineIndEtale.ker i)

/-- Reindex an affine ind-étale object over `Z` to an ind-étale algebra over
`Γ(X, ⊤) ⧸ ker i`. -/
def AffineIndEtale.toQuotientIndEtale (i : Z ⟶ X) [IsClosedImmersion i] (V : AffineIndEtale Z) :
    CommAlgCat.IndEtale.{u} (Γ(X, ⊤) ⧸ AffineIndEtale.ker i) :=
  (CommAlgCat.IndEtale.reindex (AffineIndEtale.quotientIso i).symm).obj
    ((AffineIndEtale.toIndEtale Z).obj V).unop

/-- The left adjoint of affine ind-étale base change, sending `V` to the
spectrum of the ind-étale lift of `Γ(V, ⊤)`. -/
def AffineIndEtale.lift (i : Z ⟶ X) [IsClosedImmersion i] : AffineIndEtale Z ⥤ AffineIndEtale X :=
  AffineIndEtale.toIndEtale Z ⋙ (algebraLift i).op ⋙ AffineIndEtale.ofIndEtale X

/-- `lift` is `ofIndEtale` of the algebra-level lift of `toIndEtale`. -/
theorem AffineIndEtale.lift_obj (i : Z ⟶ X) [IsClosedImmersion i] (V : AffineIndEtale Z) :
    (AffineIndEtale.lift i).obj V =
      (AffineIndEtale.ofIndEtale X).obj
        (op ((algebraLift i).obj ((AffineIndEtale.toIndEtale Z).obj V).unop)) :=
  rfl

/-- The algebra map from the lift of `Γ(V, ⊤)` to `Γ(V, ⊤)` itself. -/
def AffineIndEtale.liftι_appTop (i : Z ⟶ X) [IsClosedImmersion i] (V : AffineIndEtale Z) :
    ((algebraLift i).obj ((AffineIndEtale.toIndEtale Z).obj V).unop : Type u) →+*
      Γ(V.obj.left, ⊤) :=
  (colimit.desc
      (CommAlgCat.IndEtale.diagram Γ(X, ⊤) (toQuotientIndEtale i V))
      (CommAlgCat.IndEtale.toTargetCocone Γ(X, ⊤)
        (toQuotientIndEtale i V))).hom.toRingHom

/-- The comparison morphism `V ⟶ v(V)` on underlying schemes. -/
def AffineIndEtale.liftι (i : Z ⟶ X) [IsClosedImmersion i] (V : AffineIndEtale Z) :
    V.obj.left ⟶ ((AffineIndEtale.lift i).obj V).obj.left :=
  V.obj.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (liftι_appTop i V))

/-- The comparison `V ⟶ v(V)` commutes with the structure maps to `X`. -/
theorem AffineIndEtale.liftι_w (i : Z ⟶ X) [IsClosedImmersion i] (V : AffineIndEtale Z) :
    liftι i V ≫ ((AffineIndEtale.lift i).obj V).obj.hom = V.obj.hom ≫ i :=
  sorry

/-- The unit morphism of `lift ⊣ baseChange` commutes with structure maps to `Z`. -/
private theorem AffineIndEtale.liftUnitApp_w (i : Z ⟶ X) [IsClosedImmersion i] (V : AffineIndEtale Z) :
    pullback.lift (liftι i V) V.obj.hom (liftι_w i V) ≫
      ((AffineIndEtale.baseChange i).obj ((AffineIndEtale.lift i).obj V)).obj.hom =
        V.obj.hom := sorry

/-- The adjunction unit at `V`, as the pullback lift of `liftι` and `V ⟶ Z`. -/
def AffineIndEtale.liftUnitApp (i : Z ⟶ X) [IsClosedImmersion i] (V : AffineIndEtale Z) :
    V ⟶ (AffineIndEtale.baseChange i).obj ((AffineIndEtale.lift i).obj V) :=
  homMk (MorphismProperty.Over.homMk
    (pullback.lift (liftι i V) V.obj.hom (liftι_w i V))
    (by exact AffineIndEtale.liftUnitApp_w i V))

/-- The unit morphism is the pullback lift of `liftι` against the structure map. -/
theorem AffineIndEtale.liftUnitApp_left (i : Z ⟶ X) [IsClosedImmersion i] (V : AffineIndEtale Z) :
    (liftUnitApp i V).hom.left =
      pullback.lift (liftι i V) V.obj.hom (liftι_w i V) := rfl

/-- Global sections of `U ×_X Z`, as an `A`-algebra map out of `Γ(U, ⊤)`. -/
def AffineIndEtale.algebraUnitToTarget (i : Z ⟶ X) [IsClosedImmersion i]
    (U : AffineIndEtale X) :
    Γ(U.obj.left, ⊤) →ₐ[Γ(X, ⊤)]
      (toQuotientIndEtale i ((AffineIndEtale.baseChange i).obj U) : Type u) :=
  { (pullback.fst U.obj.hom i).appTop.hom with commutes' := sorry }

/-- The underlying ring homomorphism of `algebraUnitToTarget` is the map on
global sections induced by the projection `U ×_X Z ⟶ U`. -/
theorem AffineIndEtale.algebraUnitToTarget_toRingHom (i : Z ⟶ X)
    [IsClosedImmersion i] (U : AffineIndEtale X) :
    (algebraUnitToTarget i U).toRingHom =
      (pullback.fst U.obj.hom i).appTop.hom := rfl

/-- The algebra map into the lift of the global sections of the pullback,
induced by the pullback projection through the ind-étale lifting eliminator. -/
def AffineIndEtale.algebraUnitApp (i : Z ⟶ X) [IsClosedImmersion i]
    (U : AffineIndEtale X) :
    ((AffineIndEtale.toIndEtale X).obj U).unop ⟶
      (algebraLift i).obj
        ((AffineIndEtale.toIndEtale Z).obj
          ((AffineIndEtale.baseChange i).obj U)).unop :=
  homMk (CommAlgCat.ofHom
    (CommAlgCat.IndEtale.homToLift (ker i)
      ((AffineIndEtale.toIndEtale X).obj U).unop
      (toQuotientIndEtale i ((AffineIndEtale.baseChange i).obj U))
      (algebraUnitToTarget i U)))

/-- The underlying algebra map into the lift is the explicit ind-étale lifting eliminator. -/
theorem AffineIndEtale.algebraUnitApp_hom (i : Z ⟶ X) [IsClosedImmersion i]
    (U : AffineIndEtale X) :
    (algebraUnitApp i U).hom = CommAlgCat.ofHom
      (CommAlgCat.IndEtale.homToLift (ker i)
        ((AffineIndEtale.toIndEtale X).obj U).unop
        (toQuotientIndEtale i ((AffineIndEtale.baseChange i).obj U))
        (algebraUnitToTarget i U)) := rfl

/-- The adjunction `v ⊣ u` between affine ind-étale sites. -/
def AffineIndEtale.liftAdjunction (i : Z ⟶ X) [IsClosedImmersion i] :
    AffineIndEtale.lift i ⊣ AffineIndEtale.baseChange i :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun V U =>
        { toFun := fun f =>
            liftUnitApp i V ≫ (AffineIndEtale.baseChange i).map f
          invFun := fun g =>
            (AffineIndEtale.ofIndEtale X).map
                (algebraUnitApp i U ≫
                    (algebraLift i).map
                      ((AffineIndEtale.toIndEtale Z).map g).unop).op ≫
              AffineIndEtale.ofIndEtaleCounitApp X U
          left_inv := sorry
          right_inv := sorry }
      homEquiv_naturality_left_symm := sorry
      homEquiv_naturality_right := sorry }

/-- The forward adjunction equivalence is postcomposition with the unit. -/
theorem AffineIndEtale.liftAdjunction_homEquiv_apply (i : Z ⟶ X) [IsClosedImmersion i] {V : AffineIndEtale Z}
    {U : AffineIndEtale X} (f : (AffineIndEtale.lift i).obj V ⟶ U) :
    (liftAdjunction i).homEquiv V U f =
      liftUnitApp i V ≫ (AffineIndEtale.baseChange i).map f := by
  unfold liftAdjunction
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- The affine ind-étale lift is fully faithful, with preimages formed by
composing reverse scalar transport, algebraic reduction, and affine comparison maps. -/
def AffineIndEtale.liftFullyFaithful (i : Z ⟶ X) [IsClosedImmersion i] :
    (AffineIndEtale.lift i).FullyFaithful :=
  (AffineIndEtale.toIndEtaleFullyFaithful Z).comp
    (((CommAlgCat.IndEtale.reindexFullyFaithful (quotientIso i).symm).comp
      (CommAlgCat.IndEtale.liftFullyFaithful (ker i))).op.comp
        (AffineIndEtale.ofIndEtaleFullyFaithful X))

/-- Affine ind-étale lift is a full functor. -/
instance AffineIndEtale.lift_full (i : Z ⟶ X) [IsClosedImmersion i] :
    (AffineIndEtale.lift i).Full := (liftFullyFaithful i).full

/-- Affine ind-étale lift is a faithful functor. -/
instance AffineIndEtale.lift_faithful (i : Z ⟶ X) [IsClosedImmersion i] :
    (AffineIndEtale.lift i).Faithful := (liftFullyFaithful i).faithful

/-- Affine ind-étale lift is left adjoint to base change. -/
instance AffineIndEtale.lift_isLeftAdjoint (i : Z ⟶ X) [IsClosedImmersion i] : (AffineIndEtale.lift i).IsLeftAdjoint where
  exists_rightAdjoint := ⟨AffineIndEtale.baseChange i, ⟨liftAdjunction i⟩⟩

/-- The fully faithful preimage recovers morphisms of affine ind-étale objects. -/
theorem AffineIndEtale.liftFullyFaithful_preimage_map (i : Z ⟶ X)
    [IsClosedImmersion i] {V W : AffineIndEtale Z} (f : V ⟶ W) :
    (liftFullyFaithful i).preimage ((AffineIndEtale.lift i).map f) = f :=
  (liftFullyFaithful i).preimage_map f

/-- The comparison `V ⟶ v(V)` is a closed immersion. -/
instance AffineIndEtale.liftι_isClosedImmersion (i : Z ⟶ X) [IsClosedImmersion i]
    (V : AffineIndEtale Z) :
    IsClosedImmersion (AffineIndEtale.liftι i V) := sorry

/-- The comparison identifies `V` with the fibre product `v(V) ×_X Z`. -/
theorem AffineIndEtale.liftι_isPullback (i : Z ⟶ X) [IsClosedImmersion i]
    (V : AffineIndEtale Z) :
    IsPullback V.obj.hom (AffineIndEtale.liftι i V) i
      ((AffineIndEtale.lift i).obj V).obj.hom := sorry

/-- The adjunction unit identifies `V` with `u(v(V))`. -/
instance AffineIndEtale.lift_unit_isIso (i : Z ⟶ X) [IsClosedImmersion i]
    (V : AffineIndEtale Z) :
    IsIso ((AffineIndEtale.liftAdjunction i).unit.app V) := sorry

/-- Every point of `v(V)` specializes to a point of `V`. -/
theorem AffineIndEtale.liftι_specializes (i : Z ⟶ X) [IsClosedImmersion i]
    (V : AffineIndEtale Z) (x : ((AffineIndEtale.lift i).obj V).obj.left) :
    ∃ y : V.obj.left, x ⤳ AffineIndEtale.liftι i V y := sorry

/-- Affine ind-étale lift is cocontinuous. -/
instance AffineIndEtale.lift_isCocontinuous (i : Z ⟶ X) [IsClosedImmersion i] :
    Functor.IsCocontinuous (AffineIndEtale.lift i)
      (affineIndEtaleTopology Z) (affineIndEtaleTopology X) := sorry

/-- Affine ind-étale lift sends covering families to covering families. -/
theorem AffineIndEtale.lift_map_mem_precoverage (i : Z ⟶ X) [IsClosedImmersion i]
    {V : AffineIndEtale Z} {R : Presieve V}
    (hR : R ∈ affineIndEtalePrecoverage Z V) :
    R.map (AffineIndEtale.lift i) ∈
      affineIndEtalePrecoverage X ((AffineIndEtale.lift i).obj V) := sorry

/-- Topology-level covering preservation for affine ind-étale lift. -/
theorem AffineIndEtale.lift_coverPreserving (i : Z ⟶ X) [IsClosedImmersion i] :
    CoverPreserving (affineIndEtaleTopology Z) (affineIndEtaleTopology X)
      (AffineIndEtale.lift i) := sorry

end AlgebraicGeometry.Scheme.ProEt
