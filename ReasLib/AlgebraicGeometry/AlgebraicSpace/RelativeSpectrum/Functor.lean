module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Algebra.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.Atlas
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.CommRingHom
public import Mathlib.CategoryTheory.Yoneda

/-!
# The algebraic-space relative-spectrum functor of points

Scheme-valued points are their actual base morphisms and descended atlas algebra
maps. The algebra targets and composition maps use the canonical commutative
structure sheaf and direct-image owners; representability and concrete atlases
are constructed in the surrounding relative-spectrum leaves.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry Functor CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The `𝒪_X`-algebra `g_* 𝒪_T` associated to a test morphism `g : ofOver T ⟶ X`. -/
def relativeSpectrumTarget {X : AlgebraicSpace S} {T : Over S} (g : ofOver T ⟶ X) :
    Under (commStructureSheaf X) :=
  Under.mk (commStructureSheafMap g)

/-- The comparison `T ×_Y W ⟶ X ×_Y W` induced by `t : ofOver T ⟶ X`. -/
def etaleBaseChangeMapOfPrecomp {X Y : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ X) (f : X ⟶ Y) (W : smallEtaleSite Y) :
    etaleBaseChangeSpace (t ≫ f) W ⟶ etaleBaseChangeSpace f W :=
  pullback.map (homFunctor (t ≫ f)) (homFunctor W.hom) (homFunctor f) (homFunctor W.hom)
    t (𝟙 _) (𝟙 _) sorry sorry

/-- After composing with the first projection, `etaleBaseChangeMapOfPrecomp t f W` recovers
`t` on the `T`-factor. -/
theorem etaleBaseChangeMapOfPrecomp_comp_fst {X Y : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ X) (f : X ⟶ Y) (W : smallEtaleSite Y) :
    etaleBaseChangeMapOfPrecomp t f W ≫ etaleBaseChangeHom f W =
      etaleBaseChangeHom (t ≫ f) W ≫ t :=
  sorry

/-- The pullback-associator `T ×_Y W ⟶ T ×_X (X ×_Y W)` as a morphism of algebraic spaces. -/
def etaleBaseChangeAssocHom {X Y : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ X) (f : X ⟶ Y) (W : smallEtaleSite Y) :
    etaleBaseChangeSpace (t ≫ f) W ⟶ pullback (etaleBaseChangeHom f W) t :=
  pullback.lift (etaleBaseChangeMapOfPrecomp t f W) (etaleBaseChangeHom (t ≫ f) W) sorry

/-- The associator projects to `T ×_Y W ⟶ X ×_Y W` along `pullback.fst`. -/
theorem etaleBaseChangeAssocHom_fst {X Y : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ X) (f : X ⟶ Y) (W : smallEtaleSite Y) :
    etaleBaseChangeAssocHom t f W ≫ pullback.fst (etaleBaseChangeHom f W) t =
      etaleBaseChangeMapOfPrecomp t f W :=
  sorry

/-- The associator `T ×_Y W ⟶ T ×_X (X ×_Y W)` in the spaces étale site of `ofOver T`. -/
def etaleBaseChangeAssoc {X Y : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ X) (f : X ⟶ Y) (W : smallEtaleSite Y) :
    etaleBaseChangeObj (t ≫ f) W ⟶
      (spacesEtalePullback t).obj (etaleBaseChangeObj f W) :=
  MorphismProperty.Over.homMk (etaleBaseChangeAssocHom t f W) sorry

/-- The underlying algebraic-space morphism of `etaleBaseChangeAssoc` is
`etaleBaseChangeAssocHom`. -/
theorem etaleBaseChangeAssoc_left {X Y : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ X) (f : X ⟶ Y) (W : smallEtaleSite Y) :
    (etaleBaseChangeAssoc t f W).left = etaleBaseChangeAssocHom t f W :=
  rfl

/-- The inverse associator `T ×_X (X ×_Y W) ⟶ T ×_Y W` as a morphism of algebraic spaces. -/
def etaleBaseChangeAssocInvHom {X Y : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ X) (f : X ⟶ Y) (W : smallEtaleSite Y) :
    pullback (etaleBaseChangeHom f W) t ⟶ etaleBaseChangeSpace (t ≫ f) W :=
  (CategoryTheory.Limits.pullback.lift
      (pullback.snd (etaleBaseChangeHom f W) t)
      (pullback.fst (etaleBaseChangeHom f W) t ≫ etaleBaseChangeSnd f W) sorry :
    (pullback (etaleBaseChangeHom f W) t).functorOfPoints ⟶
      (etaleBaseChangeSpace (t ≫ f) W).functorOfPoints)

/-- The inverse associator in the spaces étale site of `ofOver T`. -/
def etaleBaseChangeAssocInv {X Y : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ X) (f : X ⟶ Y) (W : smallEtaleSite Y) :
    (spacesEtalePullback t).obj (etaleBaseChangeObj f W) ⟶ etaleBaseChangeObj (t ≫ f) W :=
  MorphismProperty.Over.homMk (etaleBaseChangeAssocInvHom t f W) sorry

/-- The underlying algebraic-space morphism of `etaleBaseChangeAssocInv` is
`etaleBaseChangeAssocInvHom`. -/
theorem etaleBaseChangeAssocInv_left {X Y : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ X) (f : X ⟶ Y) (W : smallEtaleSite Y) :
    (etaleBaseChangeAssocInv t f W).left = etaleBaseChangeAssocInvHom t f W :=
  rfl

/-- Comparison of the functor-of-points fibre product `T ×_X V` with the categorical fibre
product used by `spacesEtalePullback`. -/
def etaleBaseChangeToSpacesPullback {X : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ X) (V : smallEtaleSite X) :
    etaleBaseChangeObj t V ⟶
      (spacesEtalePullback t).obj ((AlgebraicGeometry.AlgebraicSpace.smallEtaleToSpaces X).obj V) :=
  MorphismProperty.Over.homMk
    (pullback.lift (etaleBaseChangeSnd t V) (etaleBaseChangeHom t V) sorry) sorry

/-- The comparison `etaleBaseChangeToSpacesPullback t V` projects to `t_* V ⟶ T` along
`pullback.snd`. -/
theorem etaleBaseChangeToSpacesPullback_snd {X : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ X) (V : smallEtaleSite X) :
    (etaleBaseChangeToSpacesPullback t V).left ≫ pullback.snd V.hom t =
      etaleBaseChangeHom t V :=
  sorry

/-- The morphism `T ×_X V ⟶ T ×_Y W` associated to an arrow `V ⟶ X ×_Y W` in the spaces
étale site of `X`. -/
def etaleBaseChangeStructuredArrowHom {X Y : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ X) (f : X ⟶ Y) (W : smallEtaleSite Y)
    (a : StructuredArrow (op ((etaleBaseChange f).obj W)) (AlgebraicGeometry.AlgebraicSpace.smallEtaleToSpaces X).op) :
    (etaleBaseChange t).obj a.right.unop ⟶ (etaleBaseChange (t ≫ f)).obj W :=
  etaleBaseChangeToSpacesPullback t a.right.unop ≫
    (spacesEtalePullback t).map a.hom.unop ≫ etaleBaseChangeAssocInv t f W

/-- `etaleBaseChangeStructuredArrowHom` is the composite of the spaces-pullback comparison,
the image of the structured arrow, and the inverse associator. -/
theorem etaleBaseChangeStructuredArrowHom_eq {X Y : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ X) (f : X ⟶ Y) (W : smallEtaleSite Y)
    (a : StructuredArrow (op ((etaleBaseChange f).obj W)) (AlgebraicGeometry.AlgebraicSpace.smallEtaleToSpaces X).op) :
    etaleBaseChangeStructuredArrowHom t f W a =
      etaleBaseChangeToSpacesPullback t a.right.unop ≫
        (spacesEtalePullback t).map a.hom.unop ≫ etaleBaseChangeAssocInv t f W :=
  rfl

/-- The cone of Kan-counit components presenting `(t ≫ f)_* 𝒪_T ⟶ f_* (t_* 𝒪_T)` at `W`. -/
def commRingPushforwardPrecompCounitCone {X Y : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ X) (f : X ⟶ Y) (W : smallEtaleSite Y) :
    Cone (StructuredArrow.proj (op ((etaleBaseChange f).obj W))
        (AlgebraicGeometry.AlgebraicSpace.smallEtaleToSpaces X).op ⋙
          ((commRingPushforward t).obj (commStructureSheaf (ofOver T))).obj) where
  pt :=
    ((commRingPushforward (t ≫ f)).obj (commStructureSheaf (ofOver T))).obj.obj (op W)
  π :=
    { app := fun a ↦
        ((commRingPushforwardComp t f).inv.app (commStructureSheaf (ofOver T))).hom.app (op W) ≫
          commRingPushforwardEvaluation f
            ((commRingPushforward t).obj (commStructureSheaf (ofOver T))) a.hom.unop
      naturality := fun _ _ _ ↦ sorry }

/-- The component at `W` of the Kan-counit comparison `(t ≫ f)_* 𝒪_T ⟶ f_* (t_* 𝒪_T)`. -/
def commRingPushforwardPrecompCounit_app {X Y : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ X) (f : X ⟶ Y) (W : (smallEtaleSite Y)ᵒᵖ) :
    ((commRingPushforward (t ≫ f)).obj (commStructureSheaf (ofOver T))).obj.obj W ⟶
      ((commRingPushforward f).obj
          ((commRingPushforward t).obj (commStructureSheaf (ofOver T)))).obj.obj W :=
  ((commRingPushforwardComp t f).inv.app (commStructureSheaf (ofOver T))).hom.app W

/-- `commRingPushforwardPrecompCounit_app t f W` is the limit-lift of the Kan-counit cone. -/
theorem commRingPushforwardPrecompCounit_app_eq {X Y : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ X) (f : X ⟶ Y) (W : (smallEtaleSite Y)ᵒᵖ) :
    commRingPushforwardPrecompCounit_app t f W =
      ((commRingPushforwardComp t f).inv.app (commStructureSheaf (ofOver T))).hom.app W :=
  rfl

/-- The Kan-counit comparison `(t ≫ f)_* 𝒪_T ⟶ f_* (t_* 𝒪_T)`, obtained from pullback
associativity and the pointwise limit formula for the right Kan extension. -/
def commRingPushforwardPrecompCounit {X Y : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ X) (f : X ⟶ Y) :
    (commRingPushforward (t ≫ f)).obj (commStructureSheaf (ofOver T)) ⟶
      (commRingPushforward f).obj
        ((commRingPushforward t).obj (commStructureSheaf (ofOver T))) :=
  (commRingPushforwardComp t f).inv.app (commStructureSheaf (ofOver T))

/-- The Kan-counit comparison is an isomorphism of commutative-ring sheaves. -/
instance commRingPushforwardPrecompCounit_isIso {X Y : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ X) (f : X ⟶ Y) :
    IsIso (commRingPushforwardPrecompCounit t f) :=
  inferInstanceAs (IsIso ((commRingPushforwardComp t f).inv.app (commStructureSheaf (ofOver T))))

/-- Comparison `f_* (t_* 𝒪_T) ⟶ (t ≫ f)_* 𝒪_T` obtained by inverting the Kan-counit
associator. -/
def commRingPushforwardPrecomp {X Y : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ X) (f : X ⟶ Y) :
    (commRingPushforward f).obj
        ((commRingPushforward t).obj (commStructureSheaf (ofOver T))) ⟶
      (commRingPushforward (t ≫ f)).obj (commStructureSheaf (ofOver T)) :=
  (commRingPushforwardComp t f).hom.app (commStructureSheaf (ofOver T))

/-- `commRingPushforwardPrecomp t f` is the inverse of the Kan-counit comparison. -/
theorem commRingPushforwardPrecomp_eq {X Y : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ X) (f : X ⟶ Y) :
    commRingPushforwardPrecomp t f = inv (commRingPushforwardPrecompCounit t f) := by
  apply IsIso.eq_inv_of_hom_inv_id
  exact ((commRingPushforwardComp t f).app (commStructureSheaf (ofOver T))).inv_hom_id

/-- Restriction of `g_* 𝒪_T` along a morphism of test objects `T' ⟶ T`. -/
def relativeSpectrumTargetMap {X : AlgebraicSpace S} {T T' : Over S}
    (g : ofOver T ⟶ X) (φ : T' ⟶ T) :
    relativeSpectrumTarget g ⟶ relativeSpectrumTarget ((ofOverFunctor S).map φ ≫ g) :=
  CategoryTheory.Under.homMk
    ((commRingPushforward g).map (commStructureSheafMap ((ofOverFunctor S).map φ)) ≫
      commRingPushforwardPrecomp ((ofOverFunctor S).map φ) g)
    sorry

/-- An atlas-Zariski algebra map is compatible with a kernel-pair algebra map along an atlas
kernel-pair projection when the naturality squares on images of kernel-pair opens commute. -/
def isCompatibleWithKernelPairProjection {X : AlgebraicSpace S} {A : X.QcAlgebraUnder}
    {T : Over S} {g : ofOver T ⟶ X} (φ : atlasKernelPair X ⟶ atlasScheme X)
    (hφ : IsOpenMap φ.left.base)
    (wφ : (ofOverFunctor S).map φ ≫ atlasHom X = atlasKernelPairHom X)
    (e : restrictUnder A.obj ⟶ restrictUnder (relativeSpectrumTarget g))
    (k : restrictToKernelPairPresheaf A.obj.right ⟶
      restrictToKernelPairPresheaf (relativeSpectrumTarget g).right) : Prop :=
  ∀ W : (atlasKernelPair X).left.Opens,
    e.right.app (op (atlasKernelPairImage X φ hφ W)) ≫
        (relativeSpectrumTarget g).right.obj.map (op (kernelPairOpenHom X φ hφ wφ W)) =
      A.obj.right.obj.map (op (kernelPairOpenHom X φ hφ wφ W)) ≫ k.app (op W)

/-- An atlas-Zariski `𝒪_X`-algebra map is descended when the two pullbacks along the
projections of `U ×_X U` agree as a map on the Zariski site of the kernel pair. -/
def isDescendedAtlasAlgebraMap {X : AlgebraicSpace S} {A : X.QcAlgebraUnder}
    {T : Over S} {g : ofOver T ⟶ X}
    (e : restrictUnder A.obj ⟶ restrictUnder (relativeSpectrumTarget g)) : Prop :=
  ∃ k : restrictToKernelPairPresheaf A.obj.right ⟶
      restrictToKernelPairPresheaf (relativeSpectrumTarget g).right,
    isCompatibleWithKernelPairProjection (atlasKernelPair_t X)
      (atlasKernelPair_t_isOpenMap X) rfl e k ∧
      isCompatibleWithKernelPairProjection (atlasKernelPair_s X)
      (atlasKernelPair_s_isOpenMap X) (atlasKernelPair_t_comp_eq_s_comp X).symm e k

/-- Compatibility along an atlas kernel-pair projection is the naturality square on each
kernel-pair open. -/
theorem isCompatibleWithKernelPairProjection_iff {X : AlgebraicSpace S} {A : X.QcAlgebraUnder}
    {T : Over S} {g : ofOver T ⟶ X} (φ : atlasKernelPair X ⟶ atlasScheme X)
    (hφ : IsOpenMap φ.left.base)
    (wφ : (ofOverFunctor S).map φ ≫ atlasHom X = atlasKernelPairHom X)
    (e : restrictUnder A.obj ⟶ restrictUnder (relativeSpectrumTarget g))
    (k : restrictToKernelPairPresheaf A.obj.right ⟶
      restrictToKernelPairPresheaf (relativeSpectrumTarget g).right) :
    isCompatibleWithKernelPairProjection φ hφ wφ e k ↔
      ∀ W : (atlasKernelPair X).left.Opens,
        e.right.app (op (atlasKernelPairImage X φ hφ W)) ≫
            (relativeSpectrumTarget g).right.obj.map (op (kernelPairOpenHom X φ hφ wφ W)) =
          A.obj.right.obj.map (op (kernelPairOpenHom X φ hφ wφ W)) ≫ k.app (op W) :=
  sorry

/-- Descent of an atlas algebra map is existence of a common kernel-pair algebra map compatible
with both projections. -/
theorem isDescendedAtlasAlgebraMap_iff {X : AlgebraicSpace S} {A : X.QcAlgebraUnder}
    {T : Over S} {g : ofOver T ⟶ X}
    (e : restrictUnder A.obj ⟶ restrictUnder (relativeSpectrumTarget g)) :
    isDescendedAtlasAlgebraMap e ↔
      ∃ k : restrictToKernelPairPresheaf A.obj.right ⟶
          restrictToKernelPairPresheaf (relativeSpectrumTarget g).right,
        isCompatibleWithKernelPairProjection (atlasKernelPair_t X)
      (atlasKernelPair_t_isOpenMap X) rfl e k ∧
          isCompatibleWithKernelPairProjection (atlasKernelPair_s X)
      (atlasKernelPair_s_isOpenMap X) (atlasKernelPair_t_comp_eq_s_comp X).symm e k :=
  sorry

/-- Type `u` encoding of an `𝒪_X`-algebra map `A ⟶ g_* 𝒪_T`: a morphism of the restrictions of
both algebras to the Zariski site of an étale atlas of `X` that is invariant under the two
pullbacks to the Zariski site of `U ×_X U`. -/
def relativeSpectrumAlgebraMap {X : AlgebraicSpace S} (A : X.QcAlgebraUnder)
    {T : Over S} (g : ofOver T ⟶ X) : Type u :=
  { e : restrictUnder A.obj ⟶ restrictUnder (relativeSpectrumTarget g) //
    isDescendedAtlasAlgebraMap e }

/-- The underlying atlas-Zariski morphism of a descended algebra map. -/
def relativeSpectrumAlgebraMap.val {X : AlgebraicSpace S} {A : X.QcAlgebraUnder}
    {T : Over S} {g : ofOver T ⟶ X} (e : relativeSpectrumAlgebraMap A g) :
    restrictUnder A.obj ⟶ restrictUnder (relativeSpectrumTarget g) :=
  e.1

/-- `relativeSpectrumAlgebraMap.val e` is the first component of the descended subtype. -/
theorem relativeSpectrumAlgebraMap.val_eq {X : AlgebraicSpace S} {A : X.QcAlgebraUnder}
    {T : Over S} {g : ofOver T ⟶ X} (e : relativeSpectrumAlgebraMap A g) :
    relativeSpectrumAlgebraMap.val e = e.1 :=
  rfl

/-- Restrict an `𝒪_X`-algebra map `A ⟶ g_* 𝒪_T` to the Type `u` descended atlas encoding. -/
def relativeSpectrumAlgebraMap.ofHom {X : AlgebraicSpace S} {A : X.QcAlgebraUnder}
    {T : Over S} {g : ofOver T ⟶ X} (α : A.obj ⟶ relativeSpectrumTarget g) :
    relativeSpectrumAlgebraMap A g :=
  ⟨restrictUnderMap α, sorry⟩

/-- `ofHom` is restriction of algebra maps to the descended atlas subtype. -/
theorem relativeSpectrumAlgebraMap.ofHom_val {X : AlgebraicSpace S} {A : X.QcAlgebraUnder}
    {T : Over S} {g : ofOver T ⟶ X} (α : A.obj ⟶ relativeSpectrumTarget g) :
    (relativeSpectrumAlgebraMap.ofHom α).1 = restrictUnderMap α :=
  rfl

/-- Restriction from global `𝒪_X`-algebra maps `A ⟶ g_* 𝒪_T` to descended atlas-Zariski maps
is bijective. -/
theorem relativeSpectrumAlgebraMap.restrict_bijective {X : AlgebraicSpace S}
    {A : X.QcAlgebraUnder} {T : Over S} {g : ofOver T ⟶ X} :
    Function.Bijective
      (relativeSpectrumAlgebraMap.ofHom (A := A) (g := g)) :=
  sorry

/-- Yoneda inversion recovers a morphism of algebraic spaces from its `T`-point. -/
theorem yonedaEquiv_symm_yonedaEquiv_hom {X : AlgebraicSpace S} {T : Over S}
    (toX : ofOver T ⟶ X) :
    yonedaEquiv.symm (yonedaEquiv (toX : yoneda.obj T ⟶ X.functorOfPoints)) = toX :=
  sorry

/-- A `T`-point of the relative spectrum of a quasi-coherent `𝒪_X`-algebra. -/
abbrev relativeSpectrumPair {X : AlgebraicSpace S} (A : X.QcAlgebraUnder) (T : Over S) :
    Type u :=
  Σ toX : X.functorOfPoints.obj (op T),
    relativeSpectrumAlgebraMap A (yonedaEquiv.symm toX)

/-- The actual atlas algebra map, with the proved Yoneda transport made explicit. -/
def relativeSpectrumPairAlgebraMap {X : AlgebraicSpace S} {A : X.QcAlgebraUnder} {T : Over S}
    (toX : ofOver T ⟶ X) (algebraMap : A.obj ⟶ relativeSpectrumTarget toX) :
    relativeSpectrumAlgebraMap A
      (yonedaEquiv.symm (yonedaEquiv (toX : yoneda.obj T ⟶ X.functorOfPoints))) :=
  relativeSpectrumAlgebraMap.ofHom (X := X) (A := A) (T := T)
      (g := yonedaEquiv.symm (yonedaEquiv (toX : yoneda.obj T ⟶ X.functorOfPoints)))
      (algebraMap ≫
        eqToHom
          (congrArg relativeSpectrumTarget
            (Equiv.symm_apply_apply yonedaEquiv toX).symm))

/-- Build a relative-spectrum point from a morphism to `X` and an `𝒪_X`-algebra map into the
pushforward of `𝒪_T`. -/
def relativeSpectrumPairMk {X : AlgebraicSpace S} {A : X.QcAlgebraUnder} {T : Over S}
    (toX : ofOver T ⟶ X) (algebraMap : A.obj ⟶ relativeSpectrumTarget toX) :
    relativeSpectrumPair A T :=
  ⟨yonedaEquiv (toX : yoneda.obj T ⟶ X.functorOfPoints),
    relativeSpectrumPairAlgebraMap toX algebraMap⟩

/-- The structure morphism of `relativeSpectrumPairMk g α` is the `T`-point of `X` associated
to `g`. -/
theorem relativeSpectrumPairMk_fst {X : AlgebraicSpace S} {A : X.QcAlgebraUnder} {T : Over S}
    (toX : ofOver T ⟶ X) (algebraMap : A.obj ⟶ relativeSpectrumTarget toX) :
    (relativeSpectrumPairMk toX algebraMap).1 =
      yonedaEquiv (toX : yoneda.obj T ⟶ X.functorOfPoints) :=
  rfl

/-- The algebra map of `relativeSpectrumPairMk g α` is the atlas restriction of `α`. -/
theorem relativeSpectrumPairMk_snd {X : AlgebraicSpace S} {A : X.QcAlgebraUnder} {T : Over S}
    (toX : ofOver T ⟶ X) (algebraMap : A.obj ⟶ relativeSpectrumTarget toX) :
    (relativeSpectrumPairMk toX algebraMap).2 =
      relativeSpectrumPairAlgebraMap toX algebraMap :=
  rfl

/-- Pull a relative-spectrum point back along a morphism of schemes over `S`. -/
def relativeSpectrumPairMap {X : AlgebraicSpace S} {A : X.QcAlgebraUnder} {T T' : Over S}
    (φ : T' ⟶ T) (p : relativeSpectrumPair A T) : relativeSpectrumPair A T' :=
  ⟨yonedaEquiv ((ofOverFunctor S).map φ ≫ yonedaEquiv.symm p.1 : yoneda.obj T' ⟶ X.functorOfPoints),
    cast
      (congrArg (fun γ : ofOver T' ⟶ X ↦ relativeSpectrumAlgebraMap A γ)
        (Equiv.symm_apply_apply yonedaEquiv
          ((ofOverFunctor S).map φ ≫ yonedaEquiv.symm p.1)).symm)
      ⟨p.2.1 ≫ restrictUnderMap (relativeSpectrumTargetMap (yonedaEquiv.symm p.1) φ),
        sorry⟩⟩

/-- The structure morphism of a pulled-back point is the composite with `(ofOverFunctor S).map φ`. -/
theorem relativeSpectrumPairMap_fst {X : AlgebraicSpace S} {A : X.QcAlgebraUnder}
    {T T' : Over S} (φ : T' ⟶ T) (p : relativeSpectrumPair A T) :
    (relativeSpectrumPairMap φ p).1 =
      yonedaEquiv
        (((ofOverFunctor S).map φ ≫ yonedaEquiv.symm p.1 : yoneda.obj T' ⟶ X.functorOfPoints)) :=
  sorry

/-- The action on relative-spectrum points induced by a morphism in `(Over S)ᵒᵖ`. -/
def relativeSpectrumFunctorMap {X : AlgebraicSpace S} (A : X.QcAlgebraUnder)
    {T T' : (Over S)ᵒᵖ} (i : T ⟶ T') :
    relativeSpectrumPair A T.unop → relativeSpectrumPair A T'.unop :=
  relativeSpectrumPairMap i.unop

/-- The functor of points of the relative spectrum of a quasi-coherent `𝒪_X`-algebra. -/
def relativeSpectrumFunctor {X : AlgebraicSpace S} (A : X.QcAlgebraUnder) :
    (Over S)ᵒᵖ ⥤ Type u where
  obj T := relativeSpectrumPair A T.unop
  map i := TypeCat.ofHom (relativeSpectrumFunctorMap A i)
  map_id := sorry
  map_comp := sorry

/-- Evaluating the relative-spectrum functor on a scheme over `S` recovers the point type. -/
theorem relativeSpectrumFunctor_obj {X : AlgebraicSpace S} (A : X.QcAlgebraUnder)
    (T : Over S) :
    (relativeSpectrumFunctor A).obj (op T) = relativeSpectrumPair A T :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
