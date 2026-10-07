module

public import stacks_project.Chap66.Lemma_66_27_1_Hom
public import stacks_project.Chap66.Lemma_66_28_1_Hom
public import stacks_project.Chap67.Lemma_67_20_7_AffineOver
public import stacks_project.Chap67.Lemma_67_48_1_QcAlgebra

/-!
# Affine morphisms of algebraic spaces and quasi-coherent algebras

This file states the anti-equivalence between algebraic spaces affine over an
algebraic space `X` and quasi-coherent `𝒪_X`-algebras, including its
compatibility with base change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AffineMorphismOver

/-- The cone of global-section maps presenting `𝒪_X(V) ⟶ (f_* 𝒪_Y)(V)`. -/
def structureSheafPushforwardMapCone {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    (f : Y ⟶ X) (V : smallEtaleSite X) :
    Cone (StructuredArrow.proj (op ((etaleBaseChange f).obj V))
        (smallEtaleInclusion Y).op ⋙ (commRingStructureSheaf Y).obj) where
  pt := (commRingStructureSheaf X).obj.obj (op V)
  π :=
    { app := fun a ↦ (etaleSquareOfArrow f V a).map.left.appTop
      naturality := fun _ _ _ ↦ sorry }

/-- The component at `V` of the direct-image structure-sheaf map `𝒪_X ⟶ f_* 𝒪_Y`. -/
def structureSheafPushforwardMap_app {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    (f : Y ⟶ X) (V : (smallEtaleSite X)ᵒᵖ) :
    (commRingStructureSheaf X).obj.obj V ⟶
      ((commRingPushforward f).obj (commRingStructureSheaf Y)).obj.obj V :=
  limit.lift _ (structureSheafPushforwardMapCone f V.unop) ≫
    ((smallEtaleInclusion Y).op.ranObjObjIsoLimit (commRingStructureSheaf Y).obj
        (op ((etaleBaseChange f).obj V.unop))).inv

/-- The direct-image form of `f^♯`, as a morphism of commutative-ring sheaves on
the small étale site of `X`. -/
def structureSheafPushforwardMap {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    (f : Y ⟶ X) :
    commRingStructureSheaf X ⟶
      (commRingPushforward f).obj (commRingStructureSheaf Y) :=
  InducedCategory.homMk
    { app := fun V ↦ structureSheafPushforwardMap_app f V
      naturality := fun _ _ _ ↦ sorry }

/-- The component of `structureSheafPushforwardMap f` at `V` is the limit-lift
comparison. -/
theorem structureSheafPushforwardMap_app_eq {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    (f : Y ⟶ X) (V : (smallEtaleSite X)ᵒᵖ) :
    (InducedCategory.Hom.hom (structureSheafPushforwardMap f)).app V =
      structureSheafPushforwardMap_app f V := sorry

/-- The quasi-coherent `𝒪_X`-algebra `f_* 𝒪_Y` attached to an algebraic space
affine over `X`. -/
def pushforwardQcAlgebra {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Y : AffineMorphismOver X) : X.QcAlgebraUnder where
  obj := Under.mk (structureSheafPushforwardMap Y.obj.hom)
  property := sorry

/-- The underlying algebra of `pushforwardQcAlgebra Y` is the raw pushed-forward
structure sheaf. -/
theorem pushforwardQcAlgebra_obj {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Y : AffineMorphismOver X) :
    (pushforwardQcAlgebra Y).obj =
      Under.mk (structureSheafPushforwardMap Y.obj.hom) := sorry

/-- A candidate anti-equivalence sends every algebraic space affine over `X` to the
quasi-coherent algebra obtained by pushing forward its structure sheaf. -/
def IsPushforwardEquivalence {S : Scheme.{u}} (X : AlgebraicSpace S)
    (e : (AffineMorphismOver X)ᵒᵖ ≌ X.QcAlgebraUnder) : Prop :=
  ∀ Y : AffineMorphismOver X,
    Nonempty (e.functor.obj (op Y) ≅ pushforwardQcAlgebra Y)

/-- The pushforward condition for an anti-equivalence holds exactly when it
holds objectwise for every algebraic space affine over the base. -/
theorem isPushforwardEquivalence_iff {S : Scheme.{u}} (X : AlgebraicSpace S)
    (e : (AffineMorphismOver X)ᵒᵖ ≌ X.QcAlgebraUnder) :
    IsPushforwardEquivalence X e ↔
      ∀ Y : AffineMorphismOver X,
        Nonempty (e.functor.obj (op Y) ≅ pushforwardQcAlgebra Y) := sorry

/-- Algebraic spaces affine over `X` are anti-equivalent to quasi-coherent
`𝒪_X`-algebras, with the equivalence given objectwise by pushforward of
structure sheaves. -/
theorem exists_pushforwardEquivalence {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ∃ e : (AffineMorphismOver X)ᵒᵖ ≌ X.QcAlgebraUnder,
      IsPushforwardEquivalence X e := sorry

/-- The associator identifying `T' ×_T (T ×_X W)` with `T' ×_X W` in the spaces étale
site of `T'`. -/
def commRingPushforwardPrecompAssocInv {S : Scheme.{u}}
    {T T' X : AlgebraicSpace S} (a : T' ⟶ T) (f : T ⟶ X) (W : smallEtaleSite X) :
    (spacesEtalePullback a).obj ((etaleBaseChange f).obj W) ⟶
      (etaleBaseChange (a ≫ f)).obj W :=
  (spacesEtalePullback a).map
      ((smallEtaleInclusion_comp_spacesEtalePullback f).inv.app W) ≫
    (spacesEtalePullbackComp a f).inv.app ((smallEtaleInclusion X).obj W) ≫
    (smallEtaleInclusion_comp_spacesEtalePullback (a ≫ f)).hom.app W

/-- `commRingPushforwardPrecompAssocInv` is the composite of the spaces-étale
pullback comparison, the fibre-product associator, and the étale-base-change
iso. -/
theorem commRingPushforwardPrecompAssocInv_eq {S : Scheme.{u}}
    {T T' X : AlgebraicSpace S} (a : T' ⟶ T) (f : T ⟶ X) (W : smallEtaleSite X) :
    commRingPushforwardPrecompAssocInv a f W =
      (spacesEtalePullback a).map
          ((smallEtaleInclusion_comp_spacesEtalePullback f).inv.app W) ≫
        (spacesEtalePullbackComp a f).inv.app ((smallEtaleInclusion X).obj W) ≫
        (smallEtaleInclusion_comp_spacesEtalePullback (a ≫ f)).hom.app W :=
  sorry

/-- The morphism `T' ×_T U ⟶ T' ×_X W` associated to an arrow `U ⟶ T ×_X W`. -/
def commRingPushforwardPrecompStructuredArrowHom {S : Scheme.{u}}
    {T T' X : AlgebraicSpace S} (a : T' ⟶ T) (f : T ⟶ X) (W : smallEtaleSite X)
    (α : StructuredArrow (op ((etaleBaseChange f).obj W)) (smallEtaleInclusion T).op) :
    (etaleBaseChange a).obj α.right.unop ⟶ (etaleBaseChange (a ≫ f)).obj W :=
  (smallEtaleInclusion_comp_spacesEtalePullback a).inv.app α.right.unop ≫
    (spacesEtalePullback a).map α.hom.unop ≫
    commRingPushforwardPrecompAssocInv a f W

/-- `commRingPushforwardPrecompStructuredArrowHom` is the composite of the
small-étale comparison, the image of the structured arrow, and the associator. -/
theorem commRingPushforwardPrecompStructuredArrowHom_eq {S : Scheme.{u}}
    {T T' X : AlgebraicSpace S} (a : T' ⟶ T) (f : T ⟶ X) (W : smallEtaleSite X)
    (α : StructuredArrow (op ((etaleBaseChange f).obj W)) (smallEtaleInclusion T).op) :
    commRingPushforwardPrecompStructuredArrowHom a f W α =
      (smallEtaleInclusion_comp_spacesEtalePullback a).inv.app α.right.unop ≫
        (spacesEtalePullback a).map α.hom.unop ≫
        commRingPushforwardPrecompAssocInv a f W :=
  sorry

/-- The cone of Kan-counit components presenting `(a ≫ f)_* 𝒪_{T'} ⟶ f_* (a_* 𝒪_{T'})`
at `W`. -/
def commRingPushforwardPrecompCounitCone {S : Scheme.{u}}
    {T T' X : AlgebraicSpace S} (a : T' ⟶ T) (f : T ⟶ X) (W : smallEtaleSite X) :
    Cone (StructuredArrow.proj (op ((etaleBaseChange f).obj W))
        (smallEtaleInclusion T).op ⋙
          ((commRingPushforward a).obj (commRingStructureSheaf T')).obj) where
  pt :=
    ((commRingPushforward (a ≫ f)).obj (commRingStructureSheaf T')).obj.obj (op W)
  π :=
    { app := fun α ↦
        ((smallEtaleInclusion T').op.ran.obj (commRingStructureSheaf T').obj).map
          (op (commRingPushforwardPrecompStructuredArrowHom a f W α))
      naturality := fun _ _ _ ↦ sorry }

/-- The apex of `commRingPushforwardPrecompCounitCone` is `(a ≫ f)_* 𝒪_{T'}` at `W`. -/
theorem commRingPushforwardPrecompCounitCone_pt {S : Scheme.{u}}
    {T T' X : AlgebraicSpace S} (a : T' ⟶ T) (f : T ⟶ X) (W : smallEtaleSite X) :
    (commRingPushforwardPrecompCounitCone a f W).pt =
      ((commRingPushforward (a ≫ f)).obj (commRingStructureSheaf T')).obj.obj
        (op W) :=
  sorry

/-- The Kan-counit comparison `(a ≫ f)_* 𝒪_{T'} ⟶ f_* (a_* 𝒪_{T'})`. -/
def commRingPushforwardPrecompCounit {S : Scheme.{u}}
    {T T' X : AlgebraicSpace S} (a : T' ⟶ T) (f : T ⟶ X) :
    (commRingPushforward (a ≫ f)).obj (commRingStructureSheaf T') ⟶
      (commRingPushforward f).obj
        ((commRingPushforward a).obj (commRingStructureSheaf T')) :=
  InducedCategory.homMk
    { app := fun W ↦
        limit.lift _ (commRingPushforwardPrecompCounitCone a f W.unop) ≫
          ((smallEtaleInclusion T).op.ranObjObjIsoLimit
              ((commRingPushforward a).obj (commRingStructureSheaf T')).obj
              (op ((etaleBaseChange f).obj W.unop))).inv
      naturality := fun _ _ _ ↦ sorry }

/-- The component at `W` of `commRingPushforwardPrecompCounit` is the limit-lift
of the Kan-counit cone. -/
theorem commRingPushforwardPrecompCounit_app {S : Scheme.{u}}
    {T T' X : AlgebraicSpace S} (a : T' ⟶ T) (f : T ⟶ X) (W : (smallEtaleSite X)ᵒᵖ) :
    (InducedCategory.Hom.hom (commRingPushforwardPrecompCounit a f)).app W =
      limit.lift _ (commRingPushforwardPrecompCounitCone a f W.unop) ≫
        ((smallEtaleInclusion T).op.ranObjObjIsoLimit
            ((commRingPushforward a).obj (commRingStructureSheaf T')).obj
            (op ((etaleBaseChange f).obj W.unop))).inv :=
  sorry

/-- The Kan-counit comparison is an isomorphism of commutative-ring sheaves. -/
instance commRingPushforwardPrecompCounit_isIso {S : Scheme.{u}}
    {T T' X : AlgebraicSpace S} (a : T' ⟶ T) (f : T ⟶ X) :
    IsIso (commRingPushforwardPrecompCounit a f) :=
  sorry

/-- Comparison `f_* (a_* 𝒪_{T'}) ⟶ (a ≫ f)_* 𝒪_{T'}` obtained by inverting the
Kan-counit associator. -/
def commRingPushforwardPrecomp {S : Scheme.{u}} {T T' X : AlgebraicSpace S}
    (a : T' ⟶ T) (f : T ⟶ X) :
    (commRingPushforward f).obj
        ((commRingPushforward a).obj (commRingStructureSheaf T')) ⟶
      (commRingPushforward (a ≫ f)).obj (commRingStructureSheaf T') :=
  inv (commRingPushforwardPrecompCounit a f)

/-- `commRingPushforwardPrecomp` is the inverse of the Kan-counit comparison. -/
theorem commRingPushforwardPrecomp_eq {S : Scheme.{u}} {T T' X : AlgebraicSpace S}
    (a : T' ⟶ T) (f : T ⟶ X) :
    commRingPushforwardPrecomp a f = inv (commRingPushforwardPrecompCounit a f) :=
  sorry

/-- The map between target algebras induced by precomposition of a test morphism. -/
def qcAlgebraPairTargetMap {S : Scheme.{u}} {X T T' : AlgebraicSpace S}
    (f : T ⟶ X) (a : T' ⟶ T) :
    Under.mk (structureSheafPushforwardMap f) ⟶
      Under.mk (structureSheafPushforwardMap (a ≫ f)) :=
  Under.homMk
    ((commRingPushforward f).map (structureSheafPushforwardMap a) ≫
      commRingPushforwardPrecomp a f)
    sorry

/-- The underlying sheaf morphism of `qcAlgebraPairTargetMap` is pushforward of
`structureSheafPushforwardMap` followed by the associator. -/
theorem qcAlgebraPairTargetMap_right {S : Scheme.{u}} {X T T' : AlgebraicSpace S}
    (f : T ⟶ X) (a : T' ⟶ T) :
    (qcAlgebraPairTargetMap f a).right =
      (commRingPushforward f).map (structureSheafPushforwardMap a) ≫
        commRingPushforwardPrecomp a f :=
  sorry

/-- A chosen pullback of a quasi-coherent algebra, specified by its universal mapping
property against structure-sheaf pushforwards. -/
structure QcAlgebraPullback {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (g : X' ⟶ X) (A : X.QcAlgebraUnder) (A' : X'.QcAlgebraUnder) where
  /-- Maps from the pulled-back algebra correspond to maps from the original algebra after
  composing with the base morphism. -/
  homEquiv :
    ∀ {T : AlgebraicSpace S} (f : T ⟶ X'),
      (A'.obj ⟶ Under.mk (structureSheafPushforwardMap f)) ≃
        (A.obj ⟶ Under.mk (structureSheafPushforwardMap (f ≫ g)))
  /-- The comparison equivalences commute with precomposition of test algebraic spaces. -/
  homEquiv_naturality :
    ∀ {T T' : AlgebraicSpace S} (f : T' ⟶ X') (a : T ⟶ T')
      (φ : A'.obj ⟶ Under.mk (structureSheafPushforwardMap f)),
      homEquiv (a ≫ f) (φ ≫ qcAlgebraPairTargetMap f a) =
        homEquiv f φ ≫ qcAlgebraPairTargetMap (f ≫ g) a

/-- Package a universal mapping property against structure-sheaf pushforwards as a
pullback of quasi-coherent algebras. -/
def QcAlgebraPullback.ofHomEquiv {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (g : X' ⟶ X) (A : X.QcAlgebraUnder) (A' : X'.QcAlgebraUnder)
    (homEquiv :
      ∀ {T : AlgebraicSpace S} (f : T ⟶ X'),
        (A'.obj ⟶ Under.mk (structureSheafPushforwardMap f)) ≃
          (A.obj ⟶ Under.mk (structureSheafPushforwardMap (f ≫ g))))
    (homEquiv_naturality :
      ∀ {T T' : AlgebraicSpace S} (f : T' ⟶ X') (a : T ⟶ T')
        (φ : A'.obj ⟶ Under.mk (structureSheafPushforwardMap f)),
        homEquiv (a ≫ f) (φ ≫ qcAlgebraPairTargetMap f a) =
          homEquiv f φ ≫ qcAlgebraPairTargetMap (f ≫ g) a) :
    QcAlgebraPullback g A A' where
  homEquiv := homEquiv
  homEquiv_naturality := homEquiv_naturality

/-- The packaged universal mapping property recovers the supplied hom-equivalence. -/
theorem QcAlgebraPullback.ofHomEquiv_homEquiv {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} (g : X' ⟶ X) (A : X.QcAlgebraUnder)
    (A' : X'.QcAlgebraUnder)
    (homEquiv :
      ∀ {T : AlgebraicSpace S} (f : T ⟶ X'),
        (A'.obj ⟶ Under.mk (structureSheafPushforwardMap f)) ≃
          (A.obj ⟶ Under.mk (structureSheafPushforwardMap (f ≫ g))))
    (homEquiv_naturality :
      ∀ {T T' : AlgebraicSpace S} (f : T' ⟶ X') (a : T ⟶ T')
        (φ : A'.obj ⟶ Under.mk (structureSheafPushforwardMap f)),
        homEquiv (a ≫ f) (φ ≫ qcAlgebraPairTargetMap f a) =
          homEquiv f φ ≫ qcAlgebraPairTargetMap (f ≫ g) a)
    {T : AlgebraicSpace S} (f : T ⟶ X') :
    (QcAlgebraPullback.ofHomEquiv g A A' homEquiv homEquiv_naturality).homEquiv f =
      homEquiv f :=
  sorry

/-- Precomposition of a test morphism corresponds, under `homEquiv`, to the named
`Under.homMk` comparison `qcAlgebraPairTargetMap`. -/
theorem QcAlgebraPullback.homEquiv_comp {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    {g : X' ⟶ X} {A : X.QcAlgebraUnder} {A' : X'.QcAlgebraUnder}
    (P : QcAlgebraPullback g A A') {T T' : AlgebraicSpace S} (f : T' ⟶ X')
    (a : T ⟶ T') (φ : A'.obj ⟶ Under.mk (structureSheafPushforwardMap f)) :
    P.homEquiv (a ≫ f) (φ ≫ qcAlgebraPairTargetMap f a) =
      P.homEquiv f φ ≫ qcAlgebraPairTargetMap (f ≫ g) a :=
  sorry

/-- A pushforward anti-equivalence is compatible with base change if every morphism of
algebraic spaces over `S` admits a pushforward anti-equivalence over the new base, a
pullback functor on quasi-coherent algebras, and a comparison isomorphism. -/
def IsBaseChangeCompatible {S : Scheme.{u}} (X : AlgebraicSpace S)
    (eX : (AffineMorphismOver X)ᵒᵖ ≌ X.QcAlgebraUnder) : Prop :=
  IsPushforwardEquivalence X eX ∧
    ∀ {X' : AlgebraicSpace S} (g : X' ⟶ X),
      ∃ (eX' : (AffineMorphismOver X')ᵒᵖ ≌ X'.QcAlgebraUnder)
        (F : X.QcAlgebraUnder ⥤ X'.QcAlgebraUnder)
        (_ : ∀ A, QcAlgebraPullback g A (F.obj A)),
        IsPushforwardEquivalence X' eX' ∧
          Nonempty ((baseChange g).op ⋙ eX'.functor ≅ eX.functor ⋙ F)

/-- Base-change compatibility consists exactly of the objectwise pushforward condition
and compatible anti-equivalence, algebra pullback, and comparison data after every
base change. -/
theorem isBaseChangeCompatible_iff {S : Scheme.{u}} (X : AlgebraicSpace S)
    (eX : (AffineMorphismOver X)ᵒᵖ ≌ X.QcAlgebraUnder) :
    IsBaseChangeCompatible X eX ↔
      IsPushforwardEquivalence X eX ∧
        ∀ {X' : AlgebraicSpace S} (g : X' ⟶ X),
          ∃ (eX' : (AffineMorphismOver X')ᵒᵖ ≌ X'.QcAlgebraUnder)
            (F : X.QcAlgebraUnder ⥤ X'.QcAlgebraUnder)
            (_ : ∀ A, QcAlgebraPullback g A (F.obj A)),
            IsPushforwardEquivalence X' eX' ∧
              Nonempty ((baseChange g).op ⋙ eX'.functor ≅ eX.functor ⋙ F) :=
  sorry

/-- Every algebraic space admits a pushforward anti-equivalence between algebraic
spaces affine over it and quasi-coherent algebras that is compatible with
arbitrary base change. -/
theorem exists_baseChangeCompatiblePushforwardEquivalence {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    ∃ eX : (AffineMorphismOver X)ᵒᵖ ≌ X.QcAlgebraUnder,
      IsBaseChangeCompatible X eX := sorry

end AlgebraicGeometry.AlgebraicSpace.AffineMorphismOver
