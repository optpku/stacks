/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Limits
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap66.Lemma_66_18_8_Pullback
public import stacks_project.Chap66.Lemma_66_27_1_Hom
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Lemma_67_4_8
public import stacks_project.Chap67.Lemma_67_8_5
public import stacks_project.Chap67.Lemma_67_9_7
public import stacks_project.Chap67.Lemma_67_13_3
public import stacks_project.Chap67.Lemma_67_13_4
public import stacks_project.Chap67.Lemma_67_17_2_InverseImage
public import stacks_project.Chap67.Lemma_67_45_7
public import stacks_project.Chap67.Remark_67_20_9_Factorization
public import stacks_project.Chap71.Lemma_71_4_1_Fiber

/-!
# Glueing factorization of an integral morphism at a closed field-valued point

For an integral morphism `f : X ⟶ Y` of algebraic spaces and a closed immersion
`p : Spec(k) ⟶ Y`, the quasi-coherent `𝒪_Y`-algebra obtained as the pullback of
`f_* 𝒪_X` and `p_* 𝒪_{Spec(k)}` over `(X_y ⟶ Y)_* 𝒪_{X_y}` has relative spectrum
`glueingSpec f p`. The canonical maps `toGlueing` and `fromGlueing` factor `f`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

namespace QuasiSeparated

/-- An integral morphism of algebraic spaces is quasi-separated. -/
instance of_isIntegralHom {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIntegralHom f] :
    QuasiSeparated f :=
  sorry

end QuasiSeparated

/-- The scheme-theoretic fibre inclusion of a closed field-valued point is a closed
immersion. -/
instance instIsClosedImmersion_fiberι {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (p : FieldValuedPoint Y) [IsClosedImmersion p.hom] :
    IsClosedImmersion (fiberι f p) :=
  IsClosedImmersion.of_isPullback (isPullback_fiberOver f p)

/-- The structure morphism `X_y ⟶ Y` of the scheme-theoretic fibre over `p`. -/
def fiberToY {X Y : AlgebraicSpace S} (f : X ⟶ Y) (p : FieldValuedPoint Y) :
    fieldFiber f p ⟶ Y :=
  fiberι f p ≫ f

/-- `fiberToY f p` is the composite of the fibre inclusion with `f`. -/
theorem fiberToY_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y) (p : FieldValuedPoint Y) :
    fiberToY f p = fiberι f p ≫ f :=
  rfl

/-- The fibre square identifies `fiberToY f p` with `fiberToSpec f p ≫ p.hom`. -/
theorem fiberToY_eq_fiberToSpec_comp {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (p : FieldValuedPoint Y) : fiberToY f p = fiberToSpec f p ≫ p.hom :=
  (isPullback_fiberOver f p).w

/-- The associator identifying `T' ×_T (T ×_X W)` with `T' ×_X W` in the spaces étale
site of `T'`. -/
def commRingPushforwardAssocInv {T T' X : AlgebraicSpace S} (a : T' ⟶ T) (f : T ⟶ X)
    (W : smallEtaleSite X) :
    (spacesEtalePullback a).obj ((etaleBaseChange f).obj W) ⟶
      (etaleBaseChange (a ≫ f)).obj W :=
  (spacesEtalePullback a).map
      ((smallEtaleInclusion_comp_spacesEtalePullback f).inv.app W) ≫
    (spacesEtalePullbackComp a f).inv.app ((smallEtaleInclusion X).obj W) ≫
    (smallEtaleInclusion_comp_spacesEtalePullback (a ≫ f)).hom.app W

/-- The morphism `T' ×_T U ⟶ T' ×_X W` associated to an arrow `U ⟶ T ×_X W`. -/
def commRingPushforwardAssocStructuredArrowHom {T T' X : AlgebraicSpace S}
    (a : T' ⟶ T) (f : T ⟶ X) (W : smallEtaleSite X)
    (α : StructuredArrow (op ((etaleBaseChange f).obj W)) (smallEtaleInclusion T).op) :
    (etaleBaseChange a).obj α.right.unop ⟶ (etaleBaseChange (a ≫ f)).obj W :=
  (smallEtaleInclusion_comp_spacesEtalePullback a).inv.app α.right.unop ≫
    (spacesEtalePullback a).map α.hom.unop ≫ commRingPushforwardAssocInv a f W

/-- The cone of Kan-counit components presenting `(a ≫ f)_* 𝒪_{T'} ⟶ f_* (a_* 𝒪_{T'})`
at `W`. -/
def commRingPushforwardAssocCounitCone {T T' X : AlgebraicSpace S} (a : T' ⟶ T)
    (f : T ⟶ X) (W : smallEtaleSite X) :
    Cone (StructuredArrow.proj (op ((etaleBaseChange f).obj W))
        (smallEtaleInclusion T).op ⋙
          ((commRingPushforward a).obj (commRingStructureSheaf T')).obj) where
  pt :=
    ((commRingPushforward (a ≫ f)).obj (commRingStructureSheaf T')).obj.obj (op W)
  π :=
    { app := fun α ↦
        ((commRingPushforwardComp a f).inv.app (commRingStructureSheaf T')).hom.app (op W) ≫
          commRingPushforwardEvaluation f ((commRingPushforward a).obj (commRingStructureSheaf T'))
            α.hom.unop
      naturality := fun _ _ _ ↦ sorry }

/-- The Kan-counit comparison `(a ≫ f)_* 𝒪_{T'} ⟶ f_* (a_* 𝒪_{T'})`. -/
def commRingPushforwardAssocCounit {T T' X : AlgebraicSpace S} (a : T' ⟶ T)
    (f : T ⟶ X) :
    (commRingPushforward (a ≫ f)).obj (commRingStructureSheaf T') ⟶
      (commRingPushforward f).obj
        ((commRingPushforward a).obj (commRingStructureSheaf T')) :=
  (commRingPushforwardComp a f).inv.app (commRingStructureSheaf T')

/-- The Kan-counit comparison is an isomorphism of commutative-ring sheaves. -/
instance commRingPushforwardAssocCounit_isIso {T T' X : AlgebraicSpace S}
    (a : T' ⟶ T) (f : T ⟶ X) : IsIso (commRingPushforwardAssocCounit a f) :=
  inferInstanceAs (IsIso ((commRingPushforwardComp a f).inv.app (commRingStructureSheaf T')))

/-- Comparison `f_* (a_* 𝒪_{T'}) ⟶ (a ≫ f)_* 𝒪_{T'}` obtained by inverting the
Kan-counit associator. -/
def commRingPushforwardAssoc {T T' X : AlgebraicSpace S} (a : T' ⟶ T) (f : T ⟶ X) :
    (commRingPushforward f).obj
        ((commRingPushforward a).obj (commRingStructureSheaf T')) ⟶
      (commRingPushforward (a ≫ f)).obj (commRingStructureSheaf T') :=
  (commRingPushforwardComp a f).hom.app (commRingStructureSheaf T')

/-- `commRingPushforwardAssoc` is the inverse of the Kan-counit comparison. -/
theorem commRingPushforwardAssoc_eq {T T' X : AlgebraicSpace S} (a : T' ⟶ T)
    (f : T ⟶ X) :
    commRingPushforwardAssoc a f = inv (commRingPushforwardAssocCounit a f) := by
  apply IsIso.eq_inv_of_hom_inv_id
  exact ((commRingPushforwardComp a f).app (commRingStructureSheaf T')).inv_hom_id

/-- The `𝒪_Y`-algebra map `f_* 𝒪_X ⟶ (g ≫ f)_* 𝒪_Z` induced by precomposition
with `g`. -/
def pushforwardStructureQcAlgebraMap {X Y Z : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (g : Z ⟶ X) [QuasiCompact (g ≫ f)]
    [QuasiSeparated (g ≫ f)] :
    (pushforwardStructureQcAlgebra f).obj ⟶
      (pushforwardStructureQcAlgebra (g ≫ f)).obj :=
  Under.homMk
    ((commRingPushforward f).map (commRingStructureSheafMap g) ≫
      commRingPushforwardAssoc g f)
    sorry

/-- The underlying sheaf morphism of `pushforwardStructureQcAlgebraMap` is
pushforward of `g^♯` followed by the associator. -/
theorem pushforwardStructureQcAlgebraMap_right {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (g : Z ⟶ X)
    [QuasiCompact (g ≫ f)] [QuasiSeparated (g ≫ f)] :
    (pushforwardStructureQcAlgebraMap f g).right =
      (commRingPushforward f).map (commRingStructureSheafMap g) ≫
        commRingPushforwardAssoc g f :=
  rfl

/-- `fiberToY f p` is quasi-compact. -/
instance instQuasiCompact_fiberToY {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsIntegralHom f] (p : FieldValuedPoint Y) [IsClosedImmersion p.hom] :
    QuasiCompact (fiberToY f p) :=
  inferInstanceAs (QuasiCompact (fiberι f p ≫ f))

/-- `fiberToY f p` is quasi-separated. -/
instance instQuasiSeparated_fiberToY {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsIntegralHom f] (p : FieldValuedPoint Y) [IsClosedImmersion p.hom] :
    QuasiSeparated (fiberToY f p) :=
  inferInstanceAs (QuasiSeparated (fiberι f p ≫ f))

/-- The `𝒪_Y`-algebra map `f_* 𝒪_X ⟶ (X_y ⟶ Y)_* 𝒪_{X_y}`. -/
def glueingAlgebraToFiber {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIntegralHom f]
    (p : FieldValuedPoint Y) [IsClosedImmersion p.hom] :
    (pushforwardStructureQcAlgebra f).obj ⟶
      (pushforwardStructureQcAlgebra (fiberToY f p)).obj :=
  pushforwardStructureQcAlgebraMap f (fiberι f p)

/-- The `𝒪_Y`-algebra map `p_* 𝒪_{Spec(k)} ⟶ (X_y ⟶ Y)_* 𝒪_{X_y}`. -/
def glueingPointToFiber {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIntegralHom f]
    (p : FieldValuedPoint Y) [IsClosedImmersion p.hom] :
    (pushforwardStructureQcAlgebra p.hom).obj ⟶
      (pushforwardStructureQcAlgebra (fiberToY f p)).obj :=
  Under.homMk
    ((commRingPushforward p.hom).map (commRingStructureSheafMap (fiberToSpec f p)) ≫
      commRingPushforwardAssoc (fiberToSpec f p) p.hom ≫
      eqToHom
        (congrArg (fun g ↦ (commRingPushforward g).obj (commRingStructureSheaf (fieldFiber f p)))
          (fiberToY_eq_fiberToSpec_comp f p).symm))
    sorry


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
    commRingStructureSheaf Y ⟶ glueingAlgebraSheaf f p :=
  pullback.lift (pushforwardStructureQcAlgebra f).obj.hom
    (pushforwardStructureQcAlgebra p.hom).obj.hom sorry

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
      sorry)

/-- The second projection of the glueing algebra, as an `𝒪_Y`-algebra map into
`p_* 𝒪_{Spec(k)}`. -/
def glueingAlgebra_snd {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIntegralHom f]
    (p : FieldValuedPoint Y) [IsClosedImmersion p.hom] :
    glueingAlgebra f p ⟶ pushforwardStructureQcAlgebra p.hom :=
  InducedCategory.homMk
    (Under.homMk (pullback.snd (glueingAlgebraToFiber f p).right
        (glueingPointToFiber f p).right)
      sorry)

/-- The two projections exhibit `glueingAlgebra f p` as the pullback of
`glueingAlgebraToFiber` and `glueingPointToFiber`. -/
theorem isPullback_glueingAlgebra {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsIntegralHom f] (p : FieldValuedPoint Y) [IsClosedImmersion p.hom] :
    IsPullback (glueingAlgebra_fst f p).hom (glueingAlgebra_snd f p).hom
      (glueingAlgebraToFiber f p) (glueingPointToFiber f p) :=
  sorry

/-- A morphism of quasi-coherent `𝒪_X`-algebras induces a morphism of relative
spectra in the opposite direction. -/
def relativeSpecMap {X : AlgebraicSpace S} {A B : X.QcAlgebraUnder} (φ : A ⟶ B) :
    relativeSpec B ⟶ relativeSpec A where
  app T :=
    TypeCat.ofHom fun q : relativeSpectrumPair B T.unop ↦
      ⟨q.1, ⟨restrictUnderMap φ.hom ≫ q.2.1, sorry⟩⟩
  naturality := sorry

/-- `relativeSpecMap` is compatible with the structure morphisms to `X`. -/
theorem relativeSpecMap_comp_π {X : AlgebraicSpace S} {A B : X.QcAlgebraUnder}
    (φ : A ⟶ B) : relativeSpecMap φ ≫ relativeSpecπ A = relativeSpecπ B :=
  sorry

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
    toGlueing f p ≫ fromGlueing f p = f :=
  sorry

/-- The scheme-theoretic fibre inclusion of `p` into `glueingSpec f p` is a closed
immersion. -/
instance instIsClosedImmersion_fiberι_fromGlueing {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsIntegralHom f] (p : FieldValuedPoint Y)
    [IsClosedImmersion p.hom] :
    IsClosedImmersion (fiberι (fromGlueing f p) p) :=
  inferInstance

/-- There is a unique lift of `p.hom` through `fromGlueing f p`. -/
theorem unique_fromSpec_lift {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsIntegralHom f] (p : FieldValuedPoint Y) [IsClosedImmersion p.hom] :
    ∃! σ : ofOver p.overObj ⟶ glueingSpec f p, σ ≫ fromGlueing f p = p.hom :=
  sorry

/-- `toGlueing` is an isomorphism over any open immersion into `Y` whose points are
the complement of `{p}`. -/
theorem isIso_toGlueing_over_base {X Y U : AlgebraicSpace S} (f : X ⟶ Y)
    [IsIntegralHom f] (p : FieldValuedPoint Y) [IsClosedImmersion p.hom]
    (ι : U ⟶ Y) [IsOpenImmersion ι]
    (hU : Set.range (Points.map ι) = {Points.mk p}ᶜ) :
    IsIso (openInverseImageTo (toGlueing f p) (openInverseImageι (fromGlueing f p) ι)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
