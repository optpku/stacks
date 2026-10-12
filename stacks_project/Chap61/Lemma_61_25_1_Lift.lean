/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import stacks_project.Chap61.Lemma_61_7_7_Lift
public import stacks_project.Chap61.Lemma_61_25_1_Algebra
public import stacks_project.Chap61.Lemma_61_25_1_BaseChange

/-!
# Left adjoint to affine ind-étale base change

The ind-étale algebra lift of Lemma 61.7.7 transports, via global sections and
spectra, to a fully faithful left adjoint `v` of affine ind-étale base change
along a closed immersion of affine schemes.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

variable {X Z : Scheme.{u}} [IsAffine X] [IsAffine Z]

/-- Transport of `CommAlgCat.IndEtale.lift` along `Γ(Z, ⊤) ≃ Γ(X, ⊤) ⧸ ker i`. -/
def AffineIndEtale.algebraLift (i : Z ⟶ X) [IsClosedImmersion i] :
    CommAlgCat.IndEtale.{u} Γ(Z, ⊤) ⥤ CommAlgCat.IndEtale.{u} Γ(X, ⊤) :=
  CommAlgCat.IndEtale.reindex (AffineIndEtale.quotientIso i).symm ⋙
    CommAlgCat.IndEtale.lift (AffineIndEtale.ker i)

/-- The underlying object of `algebraLift` is the algebra-level lift after
reindexing. -/
theorem AffineIndEtale.algebraLift_obj (i : Z ⟶ X) [IsClosedImmersion i] (C : CommAlgCat.IndEtale.{u} Γ(Z, ⊤)) :
    (algebraLift i).obj C =
      (CommAlgCat.IndEtale.lift (AffineIndEtale.ker i)).obj
        ((CommAlgCat.IndEtale.reindex (AffineIndEtale.quotientIso i).symm).obj C) :=
  sorry

/-- Reindex an affine ind-étale object over `Z` to an ind-étale algebra over
`Γ(X, ⊤) ⧸ ker i`. -/
def AffineIndEtale.toQuotientIndEtale (i : Z ⟶ X) [IsClosedImmersion i] (V : AffineIndEtale Z) :
    CommAlgCat.IndEtale.{u} (Γ(X, ⊤) ⧸ AffineIndEtale.ker i) :=
  (CommAlgCat.IndEtale.reindex (AffineIndEtale.quotientIso i).symm).obj
    ((AffineIndEtale.toIndEtale Z).obj V).unop

/-- The underlying carrier of `toQuotientIndEtale` is the ring of global
sections of `V`. -/
theorem AffineIndEtale.toQuotientIndEtale_obj (i : Z ⟶ X) [IsClosedImmersion i] (V : AffineIndEtale Z) :
    (toQuotientIndEtale i V).obj =
      @CommAlgCat.of (Γ(X, ⊤) ⧸ AffineIndEtale.ker i) _
        Γ(V.obj.left, ⊤) _
        (CommAlgCat.IndEtale.algebraCompRingEquiv
          (AffineIndEtale.quotientIso i).symm Γ(V.obj.left, ⊤)) := sorry

/-- The left adjoint of affine ind-étale base change, sending `V` to the
spectrum of the ind-étale lift of `Γ(V, ⊤)`. -/
def AffineIndEtale.lift (i : Z ⟶ X) [IsClosedImmersion i] : AffineIndEtale Z ⥤ AffineIndEtale X :=
  AffineIndEtale.toIndEtale Z ⋙ (algebraLift i).op ⋙ AffineIndEtale.ofIndEtale X

/-- `lift` is `ofIndEtale` of the algebra-level lift of `toIndEtale`. -/
theorem AffineIndEtale.lift_obj (i : Z ⟶ X) [IsClosedImmersion i] (V : AffineIndEtale Z) :
    (AffineIndEtale.lift i).obj V =
      (AffineIndEtale.ofIndEtale X).obj
        (op ((algebraLift i).obj ((AffineIndEtale.toIndEtale Z).obj V).unop)) :=
  sorry

/-- The algebra map from the lift of `Γ(V, ⊤)` to `Γ(V, ⊤)` itself. -/
def AffineIndEtale.liftι_appTop (i : Z ⟶ X) [IsClosedImmersion i] (V : AffineIndEtale Z) :
    ((algebraLift i).obj ((AffineIndEtale.toIndEtale Z).obj V).unop : Type u) →+*
      Γ(V.obj.left, ⊤) :=
  (colimit.desc
      (CommAlgCat.IndEtale.diagram Γ(X, ⊤) (toQuotientIndEtale i V))
      (CommAlgCat.IndEtale.toTargetCocone Γ(X, ⊤)
        (toQuotientIndEtale i V))).hom.toRingHom

/-- Unfolding lemma for `liftι_appTop`. -/
theorem AffineIndEtale.liftι_appTop_def (i : Z ⟶ X) [IsClosedImmersion i] (V : AffineIndEtale Z) :
    liftι_appTop i V =
      (colimit.desc
          (CommAlgCat.IndEtale.diagram Γ(X, ⊤) (toQuotientIndEtale i V))
          (CommAlgCat.IndEtale.toTargetCocone Γ(X, ⊤)
            (toQuotientIndEtale i V))).hom.toRingHom := sorry

/-- The comparison morphism `V ⟶ v(V)` on underlying schemes. -/
def AffineIndEtale.liftι (i : Z ⟶ X) [IsClosedImmersion i] (V : AffineIndEtale Z) :
    V.obj.left ⟶ ((AffineIndEtale.lift i).obj V).obj.left :=
  V.obj.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (liftι_appTop i V))

/-- Unfolding lemma for `liftι`. -/
theorem AffineIndEtale.liftι_def (i : Z ⟶ X) [IsClosedImmersion i] (V : AffineIndEtale Z) :
    liftι i V =
      V.obj.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (liftι_appTop i V)) :=
  sorry

/-- The comparison `V ⟶ v(V)` commutes with the structure maps to `X`. -/
theorem AffineIndEtale.liftι_w (i : Z ⟶ X) [IsClosedImmersion i] (V : AffineIndEtale Z) :
    liftι i V ≫ ((AffineIndEtale.lift i).obj V).obj.hom = V.obj.hom ≫ i :=
  sorry

/-- The unit morphism of `lift ⊣ baseChange` commutes with structure maps to `Z`. -/
theorem AffineIndEtale.liftUnitApp_w (i : Z ⟶ X) [IsClosedImmersion i] (V : AffineIndEtale Z) :
    pullback.lift (liftι i V) V.obj.hom (liftι_w i V) ≫
      ((AffineIndEtale.baseChange i).obj ((AffineIndEtale.lift i).obj V)).obj.hom =
        V.obj.hom := sorry

/-- The adjunction unit at `V`, as the pullback lift of `liftι` and `V ⟶ Z`. -/
def AffineIndEtale.liftUnitApp (i : Z ⟶ X) [IsClosedImmersion i] (V : AffineIndEtale Z) :
    V ⟶ (AffineIndEtale.baseChange i).obj ((AffineIndEtale.lift i).obj V) :=
  homMk (MorphismProperty.Over.homMk
    (pullback.lift (liftι i V) V.obj.hom (liftι_w i V))
    (liftUnitApp_w i V))

/-- The unit morphism is the pullback lift of `liftι` against the structure map. -/
theorem AffineIndEtale.liftUnitApp_left (i : Z ⟶ X) [IsClosedImmersion i] (V : AffineIndEtale Z) :
    (liftUnitApp i V).hom.left =
      pullback.lift (liftι i V) V.obj.hom (liftι_w i V) := sorry

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
      (pullback.fst U.obj.hom i).appTop.hom := sorry

/-- Descent of étale factorizations of `Γ(U, ⊤)` to `Γ(U, ⊤)` itself. -/
def AffineIndEtale.toFactorizationColimitDesc (S : Scheme.{u}) [IsAffine S]
    (U : AffineIndEtale S) :
    colimit (CommAlgCat.IndEtale.diagram Γ(S, ⊤)
        ((AffineIndEtale.toIndEtale S).obj U).unop) ⟶
      ((AffineIndEtale.toIndEtale S).obj U).unop.obj :=
  colimit.desc
    (CommAlgCat.IndEtale.diagram Γ(S, ⊤)
      ((AffineIndEtale.toIndEtale S).obj U).unop)
    (CommAlgCat.IndEtale.toTargetCocone Γ(S, ⊤)
      ((AffineIndEtale.toIndEtale S).obj U).unop)

/-- For an ind-étale algebra of global sections, the factorization cocone is
colimiting. -/
instance AffineIndEtale.toFactorizationColimitDesc_isIso (S : Scheme.{u})
    [IsAffine S] (U : AffineIndEtale S) :
    IsIso (toFactorizationColimitDesc S U) := sorry

/-- Comparison from `Γ(U, ⊤)` to the colimit of its étale factorizations. -/
def AffineIndEtale.toFactorizationColimit (S : Scheme.{u}) [IsAffine S]
    (U : AffineIndEtale S) :
    ((AffineIndEtale.toIndEtale S).obj U).unop.obj ⟶
      colimit (CommAlgCat.IndEtale.diagram Γ(S, ⊤)
        ((AffineIndEtale.toIndEtale S).obj U).unop) :=
  inv (toFactorizationColimitDesc S U)

/-- The comparison is inverse to descent of the target cocone. -/
theorem AffineIndEtale.toFactorizationColimit_comp_desc (S : Scheme.{u})
    [IsAffine S] (U : AffineIndEtale S) :
    toFactorizationColimit S U ≫ toFactorizationColimitDesc S U = 𝟙 _ := sorry

/-- The cocone of étale factorizations of `Γ(U, ⊤)` valued in the algebra lift
of `Γ(U ×_X Z, ⊤)`. -/
def AffineIndEtale.algebraUnitCocone (i : Z ⟶ X) [IsClosedImmersion i]
    (U : AffineIndEtale X) :
    Cocone (CommAlgCat.IndEtale.diagram Γ(X, ⊤)
      ((AffineIndEtale.toIndEtale X).obj U).unop) where
  pt := ((algebraLift i).obj
    ((AffineIndEtale.toIndEtale Z).obj
      ((AffineIndEtale.baseChange i).obj U)).unop).obj
  ι :=
    { app := fun P ↦
        colimit.ι
          (CommAlgCat.IndEtale.diagram Γ(X, ⊤)
            (toQuotientIndEtale i ((AffineIndEtale.baseChange i).obj U)))
          (CommAlgCat.IndEtale.Factorization.postcompose
            (algebraUnitToTarget i U) P)
      naturality := sorry }

/-- The cocone point is the underlying algebra of `algebraLift` at `U ×_X Z`. -/
theorem AffineIndEtale.algebraUnitCocone_pt (i : Z ⟶ X) [IsClosedImmersion i]
    (U : AffineIndEtale X) :
    (algebraUnitCocone i U).pt =
      ((algebraLift i).obj
        ((AffineIndEtale.toIndEtale Z).obj
          ((AffineIndEtale.baseChange i).obj U)).unop).obj := sorry

/-- The algebra-level unit of reduction ⊣ lift at `Γ(U, ⊤)`, obtained by
comparing `Γ(U, ⊤)` with its factorization colimit and descending into the
lift of `Γ(U ×_X Z, ⊤)`. -/
def AffineIndEtale.algebraUnitApp (i : Z ⟶ X) [IsClosedImmersion i]
    (U : AffineIndEtale X) :
    ((AffineIndEtale.toIndEtale X).obj U).unop ⟶
      (algebraLift i).obj
        ((AffineIndEtale.toIndEtale Z).obj
          ((AffineIndEtale.baseChange i).obj U)).unop :=
  homMk (toFactorizationColimit X U ≫
    colimit.desc
      (CommAlgCat.IndEtale.diagram Γ(X, ⊤)
        ((AffineIndEtale.toIndEtale X).obj U).unop)
      (algebraUnitCocone i U))

/-- The underlying algebra map of `algebraUnitApp` is comparison followed by
descent of the postcomposed factorization cocone. -/
theorem AffineIndEtale.algebraUnitApp_hom (i : Z ⟶ X) [IsClosedImmersion i]
    (U : AffineIndEtale X) :
    (algebraUnitApp i U).hom =
      toFactorizationColimit X U ≫
        colimit.desc
          (CommAlgCat.IndEtale.diagram Γ(X, ⊤)
            ((AffineIndEtale.toIndEtale X).obj U).unop)
          (algebraUnitCocone i U) := sorry

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
      liftUnitApp i V ≫ (AffineIndEtale.baseChange i).map f := sorry

/-- Affine ind-étale lift is a full functor. -/
instance AffineIndEtale.lift_full (i : Z ⟶ X) [IsClosedImmersion i] : (AffineIndEtale.lift i).Full := sorry

/-- Affine ind-étale lift is a faithful functor. -/
instance AffineIndEtale.lift_faithful (i : Z ⟶ X) [IsClosedImmersion i] : (AffineIndEtale.lift i).Faithful := sorry

/-- Affine ind-étale lift is left adjoint to base change. -/
instance AffineIndEtale.lift_isLeftAdjoint (i : Z ⟶ X) [IsClosedImmersion i] : (AffineIndEtale.lift i).IsLeftAdjoint where
  exists_rightAdjoint := ⟨AffineIndEtale.baseChange i, ⟨liftAdjunction i⟩⟩

/-- Bundled full faithfulness of affine ind-étale lift. -/
def AffineIndEtale.liftFullyFaithful (i : Z ⟶ X) [IsClosedImmersion i] : (AffineIndEtale.lift i).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful (AffineIndEtale.lift i)

/-- The fully faithful preimage recovers morphisms of affine ind-étale objects. -/
theorem AffineIndEtale.liftFullyFaithful_preimage_map (i : Z ⟶ X)
    [IsClosedImmersion i] {V W : AffineIndEtale Z} (f : V ⟶ W) :
    (liftFullyFaithful i).preimage ((AffineIndEtale.lift i).map f) = f := sorry

end AlgebraicGeometry.Scheme.ProEt
