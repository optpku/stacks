/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Algebra.PushforwardMap
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldFiber.ClosedImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.Map
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.Factorization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine.Qcqs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.ClosedImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import Mathlib.CategoryTheory.Sites.Limits

/-!
# Glueing an integral morphism at a closed field-valued point

The pullback of the pushforward structure algebras of a morphism and a closed
field-valued point over that of their fibre defines a relative spectrum through
which the morphism factors.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The `𝒪_Y`-algebra map `f_* 𝒪_X ⟶ (X_y ⟶ Y)_* 𝒪_{X_y}`. -/
def glueingAlgebraToFiber {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIntegralHom f]
    (p : FieldValuedPoint Y) [IsClosedImmersion p.hom] :
    (pushforwardStructureQcAlgebra f).obj ⟶
      (pushforwardStructureQcAlgebra (fieldFiberι f p ≫ f)).obj :=
  pushforwardStructureQcAlgebraMap f (fieldFiberι f p)

set_option backward.isDefEq.respectTransparency false in
/-- The `𝒪_Y`-algebra map `p_* 𝒪_{Spec(k)} ⟶ (X_y ⟶ Y)_* 𝒪_{X_y}`. -/
def glueingPointToFiber {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIntegralHom f]
    (p : FieldValuedPoint Y) [IsClosedImmersion p.hom] :
    (pushforwardStructureQcAlgebra p.hom).obj ⟶
      (pushforwardStructureQcAlgebra (fieldFiberι f p ≫ f)).obj :=
  Under.homMk
    ((commRingPushforward p.hom).map (commStructureSheafMap (fieldFiberToSpec f p)) ≫
      (commRingPushforwardComp (fieldFiberToSpec f p) p.hom).hom.app
        (commStructureSheaf (fieldFiber f p)) ≫
      eqToHom
        (congrArg (fun g ↦ (commRingPushforward g).obj (commStructureSheaf (fieldFiber f p)))
          (fieldFiberι_comp f p).symm))
    (by
      haveI : QuasiCompact (fieldFiberToSpec f p ≫ p.hom) := by
        rw [← fieldFiberι_comp f p]
        infer_instance
      haveI : QuasiSeparated (fieldFiberToSpec f p ≫ p.hom) := by
        rw [← fieldFiberι_comp f p]
        infer_instance
      have hw := (pushforwardStructureQcAlgebraMap p.hom (fieldFiberToSpec f p)).w
      change commStructureSheafMap p.hom ≫
          ((commRingPushforward p.hom).map (commStructureSheafMap (fieldFiberToSpec f p)) ≫
            (commRingPushforwardComp (fieldFiberToSpec f p) p.hom).hom.app
              (commStructureSheaf (fieldFiber f p))) =
        commStructureSheafMap (fieldFiberToSpec f p ≫ p.hom) at hw
      have heq (a b : fieldFiber f p ⟶ Y) (h : a = b) :
          commStructureSheafMap b ≫
              eqToHom
                (congrArg
                  (fun g ↦ (commRingPushforward g).obj (commStructureSheaf (fieldFiber f p)))
                  h.symm) =
            commStructureSheafMap a := by
        subst b
        simp
      change commStructureSheafMap p.hom ≫ _ = commStructureSheafMap (fieldFiberι f p ≫ f)
      simp only [← Category.assoc] at hw ⊢
      rw [hw]
      exact heq _ _ (fieldFiberι_comp f p))


/-- The sheaf of `𝒪_Y`-algebras obtained as the fibre product of `f_* 𝒪_X` and
`p_* 𝒪_{Spec(k)}` over `(X_y ⟶ Y)_* 𝒪_{X_y}`. -/
def glueingAlgebraSheaf {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIntegralHom f]
    (p : FieldValuedPoint Y) [IsClosedImmersion p.hom] :
    Sheaf (smallEtaleTopology Y) CommRingCat.{u} :=
  pullback (glueingAlgebraToFiber f p).right (glueingPointToFiber f p).right

/-- The structure morphism of the glueing algebra, as the universal map from
`𝒪_Y` into the sheaf-level pullback. -/
def glueingAlgebraStructure {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIntegralHom f]
    (p : FieldValuedPoint Y) [IsClosedImmersion p.hom] :
    commStructureSheaf Y ⟶ glueingAlgebraSheaf f p :=
  pullback.lift (pushforwardStructureQcAlgebra f).obj.hom
    (pushforwardStructureQcAlgebra p.hom).obj.hom
    ((glueingAlgebraToFiber f p).w.trans (glueingPointToFiber f p).w.symm)

/-- The quasi-coherent `𝒪_Y`-algebra `𝒜'` whose relative spectrum realises the
glueing factorization of `f` at `p`. -/
def glueingAlgebra {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIntegralHom f]
    (p : FieldValuedPoint Y) [IsClosedImmersion p.hom] : Y.QcAlgebraUnder where
  obj := Under.mk (glueingAlgebraStructure f p)
  property := sorry

/-- The first projection of the glueing algebra, as an `𝒪_Y`-algebra map into
`f_* 𝒪_X`. -/
def glueingAlgebra_fst {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIntegralHom f]
    (p : FieldValuedPoint Y) [IsClosedImmersion p.hom] :
    glueingAlgebra f p ⟶ pushforwardStructureQcAlgebra f :=
  InducedCategory.homMk
    (Under.homMk (pullback.fst (glueingAlgebraToFiber f p).right
        (glueingPointToFiber f p).right)
      (by
        change glueingAlgebraStructure f p ≫ pullback.fst _ _ = _
        exact pullback.lift_fst _ _ _))

/-- The second projection of the glueing algebra, as an `𝒪_Y`-algebra map into
`p_* 𝒪_{Spec(k)}`. -/
def glueingAlgebra_snd {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIntegralHom f]
    (p : FieldValuedPoint Y) [IsClosedImmersion p.hom] :
    glueingAlgebra f p ⟶ pushforwardStructureQcAlgebra p.hom :=
  InducedCategory.homMk
    (Under.homMk (pullback.snd (glueingAlgebraToFiber f p).right
        (glueingPointToFiber f p).right)
      (by
        change glueingAlgebraStructure f p ≫ pullback.snd _ _ = _
        exact pullback.lift_snd _ _ _))

/-- The two projections exhibit `glueingAlgebra f p` as the pullback of
`glueingAlgebraToFiber` and `glueingPointToFiber`. -/
theorem isPullback_glueingAlgebra {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsIntegralHom f] (p : FieldValuedPoint Y) [IsClosedImmersion p.hom] :
    IsPullback (glueingAlgebra_fst f p).hom (glueingAlgebra_snd f p).hom
      (glueingAlgebraToFiber f p) (glueingPointToFiber f p) := by
  apply IsPullback.of_map_of_faithful (Under.forget (commStructureSheaf Y))
  exact IsPullback.of_hasPullback _ _

/-- The relative spectrum of the glueing algebra, as an algebraic space over `S`. -/
def glueingSpec {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIntegralHom f]
    (p : FieldValuedPoint Y) [IsClosedImmersion p.hom] : AlgebraicSpace S :=
  relativeSpec (glueingAlgebra f p)

/-- `glueingSpec f p` is the relative spectrum of `glueingAlgebra f p`. -/
theorem glueingSpec_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIntegralHom f]
    (p : FieldValuedPoint Y) [IsClosedImmersion p.hom] :
    glueingSpec f p = relativeSpec (glueingAlgebra f p) :=
  rfl

/-- The first factor `X ⟶ glueingSpec f p` of the glueing factorization. -/
def toGlueing {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIntegralHom f]
    (p : FieldValuedPoint Y) [IsClosedImmersion p.hom] :
    X ⟶ glueingSpec f p :=
  Hom.toPushforwardRelativeSpec f ≫ relativeSpecMap (glueingAlgebra_fst f p)

/-- The second factor `glueingSpec f p ⟶ Y` of the glueing factorization. -/
def fromGlueing {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIntegralHom f]
    (p : FieldValuedPoint Y) [IsClosedImmersion p.hom] :
    glueingSpec f p ⟶ Y :=
  relativeSpecπ (glueingAlgebra f p)

/-- `fromGlueing f p` is the relative-spectrum projection of the glueing algebra. -/
theorem fromGlueing_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIntegralHom f]
    (p : FieldValuedPoint Y) [IsClosedImmersion p.hom] :
    fromGlueing f p = relativeSpecπ (glueingAlgebra f p) :=
  rfl

/-- The glueing maps factor `f` as `toGlueing f p ≫ fromGlueing f p`. -/
theorem toGlueing_comp_fromGlueing {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsIntegralHom f] (p : FieldValuedPoint Y) [IsClosedImmersion p.hom] :
    toGlueing f p ≫ fromGlueing f p = f := by
  apply NatTrans.ext
  funext T
  apply ConcreteCategory.hom_ext
  intro x
  change yonedaEquiv (yonedaEquiv.symm x ≫ f) = f.app T x
  simp only [yonedaEquiv_comp, Equiv.apply_symm_apply]

variable {X Y : AlgebraicSpace S}

/-- The structure morphism of the glueing space of an integral morphism is integral. -/
instance IsIntegralHom.fromGlueing (f : X ⟶ Y) [IsIntegralHom f]
    (p : FieldValuedPoint Y) [IsClosedImmersion p.hom] :
    IsIntegralHom (fromGlueing f p) :=
  sorry

/-- The first glueing factor is an isomorphism over the complement of the
scheme-theoretic fibre of the second factor. -/
theorem isIso_openInverseImageTo_toGlueing (f : X ⟶ Y) [IsIntegralHom f]
    (p : FieldValuedPoint Y) [IsClosedImmersion p.hom] {U : AlgebraicSpace S}
    (ι : U ⟶ glueingSpec f p) [IsOpenImmersion ι]
    (hU : Set.range (Points.map ι) =
      (Set.range (Points.map (fieldFiberι (fromGlueing f p) p)))ᶜ) :
    IsIso (openInverseImageTo (toGlueing f p) ι) :=
  sorry

/-- The fibre of the glueing space has exactly one underlying point, represented
by a section over the spectrum of the given field. -/
theorem existsUnique_fiberPoint_eq_residueField (f : X ⟶ Y) [IsIntegralHom f]
    (p : FieldValuedPoint Y) [IsClosedImmersion p.hom] :
    ∃ x' : Points (fieldFiber (fromGlueing f p) p),
      (∀ z : Points (fieldFiber (fromGlueing f p) p), z = x') ∧
      ∃ σ : ofOver p.overObj ⟶ fieldFiber (fromGlueing f p) p,
        σ ≫ fieldFiberToSpec (fromGlueing f p) p = 𝟙 (ofOver p.overObj) ∧
          Points.mk (FieldValuedPoint.of p.K p.structureHom σ) = x' :=
  sorry

/-- For a finite morphism with locally Noetherian target, the structure morphism
of the glueing space is finite. -/
instance IsFinite.fromGlueing (f : X ⟶ Y) [IsFinite f] [IsLocallyNoetherian Y]
    (p : FieldValuedPoint Y) [IsClosedImmersion p.hom] :
    IsFinite (fromGlueing f p) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
