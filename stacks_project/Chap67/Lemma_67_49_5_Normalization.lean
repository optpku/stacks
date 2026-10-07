module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Whiskering
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.FiniteComponents.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.FiniteComponents
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Hom
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientPresheaf
public import stacks_project.Chap65.Definition_65_9_3_EtaleEquivalence
public import stacks_project.Chap65.Lemma_65_11_1_OfEtaleSurjective
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap65.Lemma_65_9_1_KernelPair
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_25_4_Normal
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Lemma_67_37_6
public import stacks_project.Chap67.Lemma_67_37_7
public import stacks_project.Chap67.Lemma_67_39_6
public import stacks_project.Chap67.Lemma_67_49_4

/-!
# Absolute normalization of algebraic spaces

An algebraic space with finitely many irreducible components on compact opens has a
chosen absolute normalization `X.normalization` and a canonical morphism
`X.normalizationTo`, obtained by normalizing an étale presentation, forming the
étale equivalence relation `R^ν` as the one-sided fibre product of the kernel pair
along `ν_U`, and taking the Type-`u` fppf sheafification of the quotient presheaf
(matching families modulo agreement on a common fppf refinement).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An étale atlas scheme of `X` whose quasi-compact opens have finitely many irreducible
components, extracted from the class field
`HasFiniteIrreducibleComponentsOnCompactOpens.exists_finiteComponents_etaleCover`. -/
def finiteComponentsScheme {S : Scheme.{u}} (X : AlgebraicSpace S)
    [hX : HasFiniteIrreducibleComponentsOnCompactOpens X] : Over S :=
  Exists.choose hX.exists_finiteComponents_etaleCover

/-- The chosen finite-components étale atlas morphism `ofOver U ⟶ X`. -/
def finiteComponentsAtlas {S : Scheme.{u}} (X : AlgebraicSpace S)
    [hX : HasFiniteIrreducibleComponentsOnCompactOpens X] :
    ofOver (finiteComponentsScheme X) ⟶ X :=
  Exists.choose (Exists.choose_spec hX.exists_finiteComponents_etaleCover)

/-- The chosen finite-components atlas is representable and étale as a presheaf morphism. -/
theorem finiteComponentsAtlas_presheaf_etale {S : Scheme.{u}} (X : AlgebraicSpace S)
    [hX : HasFiniteIrreducibleComponentsOnCompactOpens X] :
    (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf (finiteComponentsAtlas X) :=
  (Exists.choose_spec (Exists.choose_spec hX.exists_finiteComponents_etaleCover)).1

/-- The chosen finite-components atlas is étale-locally surjective. -/
theorem finiteComponentsAtlas_locallySurjective {S : Scheme.{u}} (X : AlgebraicSpace S)
    [hX : HasFiniteIrreducibleComponentsOnCompactOpens X] :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) (finiteComponentsAtlas X) :=
  (Exists.choose_spec (Exists.choose_spec hX.exists_finiteComponents_etaleCover)).2.1

/-- The source of the chosen finite-components atlas has finitely many irreducible
components on compact opens. -/
instance instHasFiniteIrreducibleComponentsOnCompactOpens_finiteComponentsScheme
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [hX : HasFiniteIrreducibleComponentsOnCompactOpens X] :
    Scheme.HasFiniteIrreducibleComponentsOnCompactOpens (finiteComponentsScheme X).left :=
  (Exists.choose_spec (Exists.choose_spec hX.exists_finiteComponents_etaleCover)).2.2

/-- The represented kernel pair `R = U ×_X U` of the chosen finite-components atlas. -/
def finiteComponentsRelation {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    PreRelation (finiteComponentsScheme X) :=
  kernelPair (finiteComponentsAtlas X) (finiteComponentsAtlas_presheaf_etale X).rep

/-- The first projection of the chosen finite-components kernel pair is étale. -/
instance instEtale_finiteComponentsRelation_t {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    AlgebraicGeometry.Etale (finiteComponentsRelation X).t.left :=
  sorry

/-- The second projection of the chosen finite-components kernel pair is étale. -/
instance instEtale_finiteComponentsRelation_s {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    AlgebraicGeometry.Etale (finiteComponentsRelation X).s.left :=
  sorry

namespace finiteComponentsRelation

/-- The kernel-pair scheme of a finite-components atlas has finitely many irreducible
components on compact opens. -/
instance instHasFiniteIrreducibleComponentsOnCompactOpens {S : Scheme.{u}}
    (X : AlgebraicSpace S) [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    Scheme.HasFiniteIrreducibleComponentsOnCompactOpens
      (finiteComponentsRelation X).left.left :=
  Scheme.HasFiniteIrreducibleComponentsOnCompactOpens.of_smooth
    (finiteComponentsRelation X).s.left

end finiteComponentsRelation

/-- The scheme over `S` represented by the absolute normalization of `U`. -/
def overNormalization {S : Scheme.{u}} (U : Over S)
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U.left] : Over S :=
  Over.mk (U.left.normalizationTo ≫ U.hom)

/-- The morphism of schemes over `S` induced by the absolute normalization of `U`. -/
def overNormalizationTo {S : Scheme.{u}} (U : Over S)
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U.left] :
    overNormalization U ⟶ U :=
  Over.homMk U.left.normalizationTo rfl

/-- The underlying scheme of `overNormalization U` is the absolute normalization of `U`. -/
theorem overNormalization_left {S : Scheme.{u}} (U : Over S)
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U.left] :
    (overNormalization U).left = U.left.normalization :=
  sorry

/-- The absolute normalization of a scheme with finitely many irreducible components on
compact opens is a normal scheme. -/
theorem isNormal_schemeNormalization (X : Scheme.{u})
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X] :
    X.normalization.isNormal :=
  sorry

/-- An étale morphism of schemes sends generic points to generic points. -/
theorem mapsTo_genericPoints_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.Etale f] :
    Set.MapsTo f (genericPoints X) (genericPoints Y) :=
  sorry

/-- Composing the absolute normalization morphism with a generic-point-preserving map
still sends generic points to generic points. -/
theorem mapsTo_genericPoints_normalizationTo_comp {X Y : Scheme.{u}}
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X] (f : X ⟶ Y)
    (hf : Set.MapsTo f (genericPoints X) (genericPoints Y)) :
    Set.MapsTo (X.normalizationTo ≫ f) (genericPoints X.normalization) (genericPoints Y) :=
  sorry

/-- The coproduct of residue-field spectra is functorial in generic-point-preserving
morphisms of schemes. -/
def genericPointSpectrumCoproductMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : Set.MapsTo f (genericPoints X) (genericPoints Y)) :
    genericPointSpectrumCoproduct X ⟶ genericPointSpectrumCoproduct Y :=
  Sigma.desc fun η : genericPoints X ↦
    Spec.map (Scheme.Hom.residueFieldMap f η.1) ≫
      Sigma.ι (fun ξ : genericPoints Y ↦ Spec (Y.residueField ξ.1)) ⟨f η.1, hf η.2⟩

/-- `genericPointSpectrumCoproductMap f hf` is the coproduct descent of the residue-field
maps of `f` on generic points. -/
theorem genericPointSpectrumCoproductMap_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : Set.MapsTo f (genericPoints X) (genericPoints Y)) :
    genericPointSpectrumCoproductMap f hf =
      Sigma.desc fun η : genericPoints X ↦
        Spec.map (Scheme.Hom.residueFieldMap f η.1) ≫
          Sigma.ι (fun ξ : genericPoints Y ↦ Spec (Y.residueField ξ.1)) ⟨f η.1, hf η.2⟩ :=
  sorry

/-- The coproduct map of residue-field spectra intertwines the canonical morphisms to the
underlying schemes. -/
theorem genericPointSpectrumCoproductMap_comp {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : Set.MapsTo f (genericPoints X) (genericPoints Y)) :
    genericPointSpectrumCoproductMap f hf ≫ genericPointSpectrumCoproductTo Y =
      genericPointSpectrumCoproductTo X ≫ f :=
  sorry

/-- The two legs of the comparison cone to `U ×_V V^ν` agree over `V`. -/
theorem overNormalizationToPullback_lift_comm {S : Scheme.{u}} {U V : Over S}
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U.left]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens V.left]
    (g : U ⟶ V)
    (hg : Set.MapsTo g.left (genericPoints U.left) (genericPoints V.left)) :
    genericPointSpectrumCoproductMap g.left hg ≫
          (genericPointSpectrumCoproductTo V.left).toNormalization ≫
            V.left.normalizationTo =
      genericPointSpectrumCoproductTo U.left ≫ g.left :=
  sorry

/-- The second projection of the comparison lift recovers the coproduct map of `U`. -/
theorem overNormalizationToPullback_lift_snd {S : Scheme.{u}} {U V : Over S}
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U.left]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens V.left]
    (g : U ⟶ V)
    (hg : Set.MapsTo g.left (genericPoints U.left) (genericPoints V.left)) :
    pullback.lift
          (genericPointSpectrumCoproductMap g.left hg ≫
            (genericPointSpectrumCoproductTo V.left).toNormalization)
          (genericPointSpectrumCoproductTo U.left)
          (overNormalizationToPullback_lift_comm g hg) ≫
        pullback.snd V.left.normalizationTo g.left =
      genericPointSpectrumCoproductTo U.left :=
  sorry

/-- The comparison morphism from `U^ν` to the one-sided fibre product `U ×_V V^ν`
along a generic-point-preserving morphism `g`. -/
def overNormalizationToPullback_left {S : Scheme.{u}} {U V : Over S}
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U.left]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens V.left]
    (g : U ⟶ V)
    (hg : Set.MapsTo g.left (genericPoints U.left) (genericPoints V.left)) :
    U.left.normalization ⟶ pullback V.left.normalizationTo g.left :=
  (genericPointSpectrumCoproductTo U.left).normalizationDesc
    (pullback.lift
      (genericPointSpectrumCoproductMap g.left hg ≫
        (genericPointSpectrumCoproductTo V.left).toNormalization)
      (genericPointSpectrumCoproductTo U.left)
      (overNormalizationToPullback_lift_comm g hg))
    (pullback.snd V.left.normalizationTo g.left)
    (overNormalizationToPullback_lift_snd g hg).symm

/-- The unique lift of a generic-point-preserving morphism of schemes over `S` through
absolute normalization, as a morphism of schemes. -/
def overNormalizationMap_left {S : Scheme.{u}} {U V : Over S}
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U.left]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens V.left]
    (g : U ⟶ V)
    (hg : Set.MapsTo g.left (genericPoints U.left) (genericPoints V.left)) :
    U.left.normalization ⟶ V.left.normalization :=
  overNormalizationToPullback_left g hg ≫ pullback.fst V.left.normalizationTo g.left

/-- `overNormalizationMap_left g hg` is compatible with the structure morphisms to `S`. -/
theorem overNormalizationMap_w {S : Scheme.{u}} {U V : Over S}
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U.left]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens V.left]
    (g : U ⟶ V)
    (hg : Set.MapsTo g.left (genericPoints U.left) (genericPoints V.left)) :
    overNormalizationMap_left g hg ≫ (overNormalization V).hom =
      (overNormalization U).hom :=
  sorry

/-- The unique lift of a generic-point-preserving morphism of schemes over `S` through
absolute normalization. -/
def overNormalizationMap {S : Scheme.{u}} {U V : Over S}
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U.left]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens V.left]
    (g : U ⟶ V)
    (hg : Set.MapsTo g.left (genericPoints U.left) (genericPoints V.left)) :
    overNormalization U ⟶ overNormalization V :=
  Over.homMk (overNormalizationMap_left g hg) (overNormalizationMap_w g hg)

/-- The lifted morphism sits over `g` after composing with the absolute normalization
morphisms. -/
theorem overNormalizationMap_comp {S : Scheme.{u}} {U V : Over S}
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U.left]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens V.left]
    (g : U ⟶ V)
    (hg : Set.MapsTo g.left (genericPoints U.left) (genericPoints V.left)) :
    overNormalizationMap g hg ≫ overNormalizationTo V =
      overNormalizationTo U ≫ g :=
  sorry

/-- The one-sided fibre product `R ×_{s, U} U^ν` of the kernel pair along the étale
projection `s` with `ν_U`. -/
def normalizedRelationPullback {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] : Over S :=
  pullback (finiteComponentsRelation X).s
    (overNormalizationTo (finiteComponentsScheme X))

/-- The comparison from the normalized kernel pair to the one-sided fibre product
`R ×_{s, U} U^ν`. -/
def normalizedRelationToPullback {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    overNormalization (finiteComponentsRelation X).left ⟶
      normalizedRelationPullback X :=
  pullback.lift
    (overNormalizationTo (finiteComponentsRelation X).left)
    (overNormalizationMap (finiteComponentsRelation X).s
      (mapsTo_genericPoints_of_etale (finiteComponentsRelation X).s.left))
    (overNormalizationMap_comp (finiteComponentsRelation X).s
      (mapsTo_genericPoints_of_etale (finiteComponentsRelation X).s.left)).symm

/-- The first projection of `R^ν`, the unique lift of the étale projection `t` through
`ν_U`. -/
def normalizedRelationT {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    overNormalization (finiteComponentsRelation X).left ⟶
      overNormalization (finiteComponentsScheme X) :=
  overNormalizationMap (finiteComponentsRelation X).t
    (mapsTo_genericPoints_of_etale (finiteComponentsRelation X).t.left)

/-- The second projection of `R^ν`, the unique lift of the étale projection `s` through
`ν_U`. -/
def normalizedRelationS {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    overNormalization (finiteComponentsRelation X).left ⟶
      overNormalization (finiteComponentsScheme X) :=
  overNormalizationMap (finiteComponentsRelation X).s
    (mapsTo_genericPoints_of_etale (finiteComponentsRelation X).s.left)

/-- The étale equivalence relation `R^ν` on the normalized atlas of `X`, whose source is
the absolute normalization of the kernel pair and whose arrows are the unique lifts of
`t` and `s` through `ν_U`. This is the one-sided fibre product `R ×_U U^ν`, not the
two-sided pullback of `R` along `ν_U`. -/
def normalizedRelation {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    PreRelation (overNormalization (finiteComponentsScheme X)) :=
  PreRelation.ofHom (prod.lift (normalizedRelationT X) (normalizedRelationS X))

/-- The source of `normalizedRelation X` is the absolute normalization of the kernel
pair. -/
theorem normalizedRelation_left {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    (normalizedRelation X).left = overNormalization (finiteComponentsRelation X).left :=
  sorry

/-- The defining map of `normalizedRelation X` is the pair of lifted projections
`(t^ν, s^ν)`. -/
theorem normalizedRelation_hom {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    (normalizedRelation X).hom = prod.lift (normalizedRelationT X) (normalizedRelationS X) :=
  sorry

/-- The normalized presentation relation of `X` is an étale equivalence relation. -/
instance instIsEtaleEquivalenceRelation_normalizedRelation {S : Scheme.{u}}
    (X : AlgebraicSpace S) [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    PreRelation.IsEtaleEquivalenceRelation (normalizedRelation X) :=
  sorry

/-- A finitely presented algebra over the sections of an open of a scheme, encoded by a
finite generating set and a finite list of polynomial relations. -/
structure PresentedAlgebra {X : Scheme.{u}} (U : X.Opens) where
  /-- The number of polynomial generators. -/
  nvars : ℕ
  /-- The number of relations. -/
  nrels : ℕ
  /-- The relations as polynomials in `nvars` variables over `Γ(X, U)`. -/
  rels : Fin nrels → MvPolynomial (Fin nvars) Γ(X, U)

/-- The trivial finitely presented algebra `Γ(X, U)` itself. -/
def PresentedAlgebra.trivial {X : Scheme.{u}} (U : X.Opens) : PresentedAlgebra U where
  nvars := 0
  nrels := 0
  rels := fun i ↦ i.elim0

/-- Base change of a presented algebra along a ring map on sections. -/
def PresentedAlgebra.map {X Y : Scheme.{u}} {U : X.Opens} {V : Y.Opens}
    (A : PresentedAlgebra U) (φ : Γ(X, U) ⟶ Γ(Y, V)) : PresentedAlgebra V where
  nvars := A.nvars
  nrels := A.nrels
  rels i := MvPolynomial.map φ.hom (A.rels i)

/-- The Type-`u` coefficient ring of a presented algebra over an open. -/
def presentedRing {X : Scheme.{u}} {U : X.Opens} (A : PresentedAlgebra U) :
    CommRingCat.{u} :=
  .of (MvPolynomial (Fin A.nvars) Γ(X, U) ⧸ Ideal.span (Set.range A.rels))

/-- `presentedRing A` is the quotient of the polynomial ring by the presented relations. -/
theorem presentedRing_eq {X : Scheme.{u}} {U : X.Opens} (A : PresentedAlgebra U) :
    presentedRing A =
      .of (MvPolynomial (Fin A.nvars) Γ(X, U) ⧸ Ideal.span (Set.range A.rels)) :=
  sorry

/-- The spectrum of a presented algebra over an open. -/
def presentedSpec {X : Scheme.{u}} {U : X.Opens} (A : PresentedAlgebra U) : Scheme.{u} :=
  Spec (presentedRing A)

/-- `presentedSpec A` is `Spec` of `presentedRing A`. -/
theorem presentedSpec_eq {X : Scheme.{u}} {U : X.Opens} (A : PresentedAlgebra U) :
    presentedSpec A = Spec (presentedRing A) :=
  sorry

/-- The ring map `Γ(X, U) ⟶ presentedRing A` sending variables to the generators. -/
def presentedRingHomFromGamma {X : Scheme.{u}} {U : X.Opens} (A : PresentedAlgebra U) :
    CommRingCat.of Γ(X, U) ⟶ presentedRing A :=
  CommRingCat.ofHom
    ((Ideal.Quotient.mk (Ideal.span (Set.range A.rels))).comp
      (MvPolynomial.C : Γ(X, U) →+* MvPolynomial (Fin A.nvars) Γ(X, U)))

/-- The morphism `Spec (presentedRing A) ⟶ Spec Γ(X, U)` induced by the structure map. -/
def presentedToGamma {X : Scheme.{u}} {U : X.Opens} (A : PresentedAlgebra U) :
    presentedSpec A ⟶ Spec (CommRingCat.of Γ(X, U)) :=
  Spec.map (presentedRingHomFromGamma A)

/-- The morphism `Spec (presentedRing A) ⟶ X` through an affine open `U`. -/
def presentedHom {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (A : PresentedAlgebra U) : presentedSpec A ⟶ X :=
  presentedToGamma A ≫ Spec.map (CommRingCat.ofHom (RingHom.id Γ(X, U))) ≫ hU.fromSpec

/-- `presentedHom hU A` factors as the structure map of the presented algebra followed by
`hU.fromSpec`. -/
theorem presentedHom_eq {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (A : PresentedAlgebra U) :
    presentedHom hU A =
      presentedToGamma A ≫ Spec.map (CommRingCat.ofHom (RingHom.id Γ(X, U))) ≫
        hU.fromSpec :=
  sorry

/-- The presented spectrum as a scheme over `S`. -/
def presentedOver {S : Scheme.{u}} (T : Over S) {U : T.left.Opens}
    (hU : IsAffineOpen U) (A : PresentedAlgebra U) : Over S :=
  Over.mk (presentedHom hU A ≫ T.hom)

/-- The structure morphism `presentedOver T hU A ⟶ T`. -/
def presentedOverHom {S : Scheme.{u}} (T : Over S) {U : T.left.Opens}
    (hU : IsAffineOpen U) (A : PresentedAlgebra U) :
    presentedOver T hU A ⟶ T :=
  Over.homMk (presentedHom hU A) rfl

/-- The ring map on presented algebras induced by a map of coefficient rings. -/
def presentedRingHom {X Y : Scheme.{u}} {U : X.Opens} {V : Y.Opens}
    (A : PresentedAlgebra U) (φ : Γ(X, U) ⟶ Γ(Y, V)) :
    presentedRing A ⟶ presentedRing (A.map φ) :=
  CommRingCat.ofHom
    (Ideal.Quotient.lift _
      ((Ideal.Quotient.mk (Ideal.span (Set.range (A.map φ).rels))).comp
        (MvPolynomial.map φ.hom)) sorry)

/-- The morphism of presented spectra induced by a map of coefficient rings. -/
def presentedSpecMap {X Y : Scheme.{u}} {U : X.Opens} {V : Y.Opens}
    (A : PresentedAlgebra U) (φ : Γ(X, U) ⟶ Γ(Y, V)) :
    presentedSpec (A.map φ) ⟶ presentedSpec A :=
  Spec.map (presentedRingHom A φ)

/-- The morphism over `S` from a base-changed presented covering piece to the original piece. -/
def presentedOverMap {S : Scheme.{u}} {T T' : Over S} (f : T' ⟶ T)
    {U : T.left.Opens} (hU : IsAffineOpen U) (A : PresentedAlgebra U)
    {V : T'.left.Opens} (hV : IsAffineOpen V) (hle : V ≤ f.left ⁻¹ᵁ U) :
    presentedOver T' hV (A.map (f.left.appLE U V hle)) ⟶ presentedOver T hU A :=
  Over.homMk (presentedSpecMap A (f.left.appLE U V hle)) sorry

/-- An fppf matching family of sections of a Type-`u` presheaf: a jointly surjective family of
finitely presented flat morphisms `Spec A_U ⟶ T` from presented algebras over affine opens of
`T`, together with compatible sections of `F`. -/
structure FppfMatching {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u) (T : Over S) where
  /-- The affine opens of `T` equipped with presented algebras. -/
  pieces : Set (Σ U : T.left.Opens, PresentedAlgebra U)
  /-- Each supporting open is affine. -/
  isAffine : ∀ p ∈ pieces, IsAffineOpen p.1
  /-- Each presented structure morphism is flat. -/
  isFlat : ∀ p (hp : p ∈ pieces), AlgebraicGeometry.Flat (presentedHom (isAffine p hp) p.2)
  /-- Each presented structure morphism is locally of finite presentation. -/
  isLocallyOfFinitePresentation :
    ∀ p (hp : p ∈ pieces),
      AlgebraicGeometry.LocallyOfFinitePresentation (presentedHom (isAffine p hp) p.2)
  /-- The presented spectra jointly cover `T`. -/
  covers : ∀ x : T.left, ∃ p, ∃ hp : p ∈ pieces, ∃ y, presentedHom (isAffine p hp) p.2 y = x
  /-- The section of `F` on each presented covering piece. -/
  val : ∀ p (hp : p ∈ pieces), F.obj (op (presentedOver T (isAffine p hp) p.2))
  /-- The family is compatible on overlaps of covering pieces. -/
  compatible : ∀ {p q} (hp : p ∈ pieces) (hq : q ∈ pieces) {W : Over S}
    (a : W ⟶ presentedOver T (isAffine p hp) p.2)
    (b : W ⟶ presentedOver T (isAffine q hq) q.2),
    a ≫ presentedOverHom T (isAffine p hp) p.2 =
        b ≫ presentedOverHom T (isAffine q hq) q.2 →
      F.map a.op (val p hp) = F.map b.op (val q hq)

/-- The pieces of the pullback of an fppf matching family along `f : T' ⟶ T`. -/
def FppfMatching.restrictPieces {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {T T' : Over S} (f : T' ⟶ T) (s : FppfMatching F T) :
    Set (Σ U : T'.left.Opens, PresentedAlgebra U) :=
  { q | ∃ p ∈ s.pieces, ∃ (_ : IsAffineOpen q.1) (hle : q.1 ≤ f.left ⁻¹ᵁ p.1),
      q.2 = p.2.map (f.left.appLE p.1 q.1 hle) }

/-- Membership in a restricted fppf matching family unpacks to a presented piece of the
original family together with an affine open of the source contained in the preimage. -/
theorem FppfMatching.mem_restrictPieces {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {T T' : Over S} (f : T' ⟶ T) (s : FppfMatching F T)
    {q : Σ U : T'.left.Opens, PresentedAlgebra U} :
    q ∈ s.restrictPieces f ↔
      ∃ p ∈ s.pieces, ∃ (_ : IsAffineOpen q.1) (hle : q.1 ≤ f.left ⁻¹ᵁ p.1),
        q.2 = p.2.map (f.left.appLE p.1 q.1 hle) :=
  sorry

/-- The affine-open witness extracted from membership in a restricted matching family. -/
def FppfMatching.restrictIsAffine {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {T T' : Over S} (f : T' ⟶ T) (s : FppfMatching F T)
    {q : Σ U : T'.left.Opens, PresentedAlgebra U} (hq : q ∈ s.restrictPieces f) :
    IsAffineOpen q.1 :=
  Exists.choose (Exists.choose_spec hq).2

/-- The original piece extracted from membership in a restricted matching family. -/
def FppfMatching.restrictPiece {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {T T' : Over S} (f : T' ⟶ T) (s : FppfMatching F T)
    {q : Σ U : T'.left.Opens, PresentedAlgebra U} (hq : q ∈ s.restrictPieces f) :
    Σ U : T.left.Opens, PresentedAlgebra U :=
  Exists.choose hq

/-- The original piece of a restricted matching family lies in the original family. -/
def FppfMatching.restrictPiece_mem {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {T T' : Over S} (f : T' ⟶ T) (s : FppfMatching F T)
    {q : Σ U : T'.left.Opens, PresentedAlgebra U} (hq : q ∈ s.restrictPieces f) :
    s.restrictPiece f hq ∈ s.pieces :=
  (Exists.choose_spec hq).1

/-- The inclusion of a restricted affine open in the preimage of the original open. -/
def FppfMatching.restrictLE {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {T T' : Over S} (f : T' ⟶ T) (s : FppfMatching F T)
    {q : Σ U : T'.left.Opens, PresentedAlgebra U} (hq : q ∈ s.restrictPieces f) :
    q.1 ≤ f.left ⁻¹ᵁ (s.restrictPiece f hq).1 :=
  Exists.choose (Exists.choose_spec (Exists.choose_spec hq).2)

/-- The restricted presentation is the coefficient-wise base change of the original
presentation. -/
def FppfMatching.restrictPiece_map {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {T T' : Over S} (f : T' ⟶ T) (s : FppfMatching F T)
    {q : Σ U : T'.left.Opens, PresentedAlgebra U} (hq : q ∈ s.restrictPieces f) :
    q.2 = (s.restrictPiece f hq).2.map
      (f.left.appLE (s.restrictPiece f hq).1 q.1 (s.restrictLE f hq)) :=
  Exists.choose_spec (Exists.choose_spec (Exists.choose_spec hq).2)

/-- The value of a restricted matching family on a pulled-back presented piece. -/
def FppfMatching.restrictVal {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {T T' : Over S} (f : T' ⟶ T) (s : FppfMatching F T)
    (q : Σ U : T'.left.Opens, PresentedAlgebra U) (hq : q ∈ s.restrictPieces f) :
    F.obj (op (presentedOver T' (s.restrictIsAffine f hq) q.2)) :=
  F.map (eqToHom
      (congrArg (presentedOver T' (s.restrictIsAffine f hq)) (s.restrictPiece_map f hq))).op
    (F.map (presentedOverMap f (s.isAffine (s.restrictPiece f hq) (s.restrictPiece_mem f hq))
        (s.restrictPiece f hq).2 (s.restrictIsAffine f hq) (s.restrictLE f hq)).op
      (s.val (s.restrictPiece f hq) (s.restrictPiece_mem f hq)))

/-- Restriction of an fppf matching family along a morphism of schemes over `S`. -/
def FppfMatching.restrict {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u} {T T' : Over S}
    (f : T' ⟶ T) (s : FppfMatching F T) : FppfMatching F T' where
  pieces := s.restrictPieces f
  isAffine q hq := s.restrictIsAffine f hq
  isFlat := sorry
  isLocallyOfFinitePresentation := sorry
  covers := sorry
  val q hq := s.restrictVal f q hq
  compatible := sorry

/-- Affine opens of `T` with the trivial presented algebra, as fppf covering pieces. -/
def FppfMatching.trivialPieces {S : Scheme.{u}} (T : Over S) :
    Set (Σ U : T.left.Opens, PresentedAlgebra U) :=
  (fun U : T.left.Opens ↦ (⟨U, PresentedAlgebra.trivial U⟩ : Σ U, PresentedAlgebra U)) ''
    {U | IsAffineOpen U}

/-- A piece in `trivialPieces T` is supported on an affine open. -/
def FppfMatching.trivialPieces_isAffine {S : Scheme.{u}} {T : Over S}
    {p : Σ U : T.left.Opens, PresentedAlgebra U} (hp : p ∈ FppfMatching.trivialPieces T) :
    IsAffineOpen p.1 :=
  (congrArg (fun q : Σ U : T.left.Opens, PresentedAlgebra U ↦ q.1)
      (Exists.choose_spec ((Set.mem_image _ {U | IsAffineOpen U} p).mp hp)).2) ▸
    (Exists.choose_spec ((Set.mem_image _ {U | IsAffineOpen U} p).mp hp)).1

/-- The affine-open fppf matching family associated to a global section of `F`. -/
def FppfMatching.ofSection {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S}
    (x : F.obj (op T)) : FppfMatching F T where
  pieces := FppfMatching.trivialPieces T
  isAffine _ hp := FppfMatching.trivialPieces_isAffine hp
  isFlat := sorry
  isLocallyOfFinitePresentation := sorry
  covers := sorry
  val p hp := F.map (presentedOverHom T (FppfMatching.trivialPieces_isAffine hp) p.2).op x
  compatible := sorry

/-- Two fppf matching families of `F` on `T` agree on a common fppf refinement when
there is a jointly covering family of presented algebras over affine opens of `T`,
indexed through a piece of each family, each of whose structure morphisms to `T` is
flat and locally of finite presentation, that pull the two families back to equal
sections of `F`. The refinement cannot be an arbitrary jointly surjective family of
schemes over `T`: a non-flat thickening such as `Spec k ⟶ Spec k[ε]` is excluded. -/
def FppfMatching.Agree {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S}
    (s t : FppfMatching F T) : Prop :=
  ∃ (ι : Type u) (U : ι → T.left.Opens) (A : ∀ i, PresentedAlgebra (U i))
    (hU : ∀ i, IsAffineOpen (U i))
    (p : ι → Σ V : T.left.Opens, PresentedAlgebra V)
    (q : ι → Σ V : T.left.Opens, PresentedAlgebra V)
    (hp : ∀ i, p i ∈ s.pieces) (hq : ∀ i, q i ∈ t.pieces)
    (fp : ∀ i,
      presentedOver T (hU i) (A i) ⟶
        presentedOver T (s.isAffine (p i) (hp i)) (p i).2)
    (fq : ∀ i,
      presentedOver T (hU i) (A i) ⟶
        presentedOver T (t.isAffine (q i) (hq i)) (q i).2),
    (∀ i, AlgebraicGeometry.Flat (presentedHom (hU i) (A i))) ∧
      (∀ i,
        AlgebraicGeometry.LocallyOfFinitePresentation
          (presentedHom (hU i) (A i))) ∧
      (∀ i,
        fp i ≫ presentedOverHom T (s.isAffine (p i) (hp i)) (p i).2 =
          presentedOverHom T (hU i) (A i)) ∧
      (∀ i,
        fq i ≫ presentedOverHom T (t.isAffine (q i) (hq i)) (q i).2 =
          presentedOverHom T (hU i) (A i)) ∧
      (∀ x : T.left, ∃ i y, presentedHom (hU i) (A i) y = x) ∧
        ∀ i, F.map (fp i).op (s.val (p i) (hp i)) =
          F.map (fq i).op (t.val (q i) (hq i))

/-- Restriction of matching families preserves agreement on a common fppf refinement. -/
theorem FppfMatching.agree_restrict {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {T T' : Over S} (f : T' ⟶ T) {s t : FppfMatching F T} (h : s.Agree t) :
    (s.restrict f).Agree (t.restrict f) :=
  sorry

/-- Push a matching family of `F` forward along a natural transformation `F ⟶ G`. -/
def FppfMatching.mapNat {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} (η : F ⟶ G)
    {T : Over S} (s : FppfMatching F T) : FppfMatching G T where
  pieces := s.pieces
  isAffine := s.isAffine
  isFlat := s.isFlat
  isLocallyOfFinitePresentation := s.isLocallyOfFinitePresentation
  covers := s.covers
  val p hp := η.app (op (presentedOver T (s.isAffine p hp) p.2)) (s.val p hp)
  compatible := sorry

/-- Forward images of agreeing matching families still agree. -/
theorem FppfMatching.agree_mapNat {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u}
    (η : F ⟶ G) {T : Over S} {s t : FppfMatching F T} (h : s.Agree t) :
    (s.mapNat η).Agree (t.mapNat η) :=
  sorry

/-- The covering arrows of an fppf matching family. -/
def FppfMatching.arrow {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S}
    (s : FppfMatching F T) (p : s.pieces) :
    presentedOver T (s.isAffine p.1 p.2) p.1.2 ⟶ T :=
  presentedOverHom T (s.isAffine p.1 p.2) p.1.2

/-- The Type-`u` plus construction: matching families of presented fppf covers, quotiented
by agreement on a common fppf refinement. -/
def plusTypeU {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u) :
    (Over S)ᵒᵖ ⥤ Type u where
  obj T := Quot (fun s t : FppfMatching F T.unop ↦ s.Agree t)
  map {T T'} f :=
    TypeCat.ofHom <|
      Quot.map (fun s : FppfMatching F T.unop ↦ s.restrict f.unop)
        fun _ _ h ↦ FppfMatching.agree_restrict f.unop h
  map_id := sorry
  map_comp := sorry

/-- The value of the plus construction is the quotient of matching families by agreement
on a common fppf refinement. -/
theorem plusTypeU_obj {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u) (T : (Over S)ᵒᵖ) :
    (plusTypeU F).obj T = Quot (fun s t : FppfMatching F T.unop ↦ s.Agree t) :=
  sorry

/-- The unit of the plus construction, sending a global section to the class of its
affine-open matching family. -/
def toPlusTypeU {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u) : F ⟶ plusTypeU F where
  app T := TypeCat.ofHom fun x ↦ Quot.mk _ (FppfMatching.ofSection x)
  naturality := sorry

/-- Functoriality of the plus construction on morphisms of Type-`u` presheaves. -/
def plusTypeUMap {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} (η : F ⟶ G) :
    plusTypeU F ⟶ plusTypeU G where
  app T :=
    TypeCat.ofHom <|
      Quot.map (fun s : FppfMatching F T.unop ↦ s.mapNat η)
        fun _ _ h ↦ FppfMatching.agree_mapNat η h
  naturality := sorry

/-- The amalgamation of a matching family of sections of an fppf sheaf along its
presented covering arrows. -/
def FppfMatching.amalgamate {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} (η : F ⟶ G)
    (hG : Presheaf.IsSheaf (Scheme.fppfTopology.over S) G) {T : Over S}
    (s : FppfMatching F T) : G.obj (op T) :=
  (hG.amalgamateOfArrows (fun p : s.pieces ↦ s.arrow p) sorry
    (fun p ↦ TypeCat.ofHom fun _ : PUnit.{u + 1} ↦
      η.app (op (presentedOver T (s.isAffine p.1 p.2) p.1.2)) (s.val p.1 p.2))
    sorry) PUnit.unit

/-- Agreeing matching families amalgamate to the same section of a sheaf. -/
theorem FppfMatching.amalgamate_agree {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u}
    (η : F ⟶ G) (hG : Presheaf.IsSheaf (Scheme.fppfTopology.over S) G) {T : Over S}
    {s t : FppfMatching F T} (h : s.Agree t) :
    s.amalgamate η hG = t.amalgamate η hG :=
  sorry

/-- The lift of a morphism into an fppf sheaf through the plus construction. -/
def plusTypeULift {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} (η : F ⟶ G)
    (hG : Presheaf.IsSheaf (Scheme.fppfTopology.over S) G) :
    plusTypeU F ⟶ G where
  app T :=
    TypeCat.ofHom <|
      Quot.lift (fun s : FppfMatching F T.unop ↦ s.amalgamate η hG)
        fun _ _ h ↦ FppfMatching.amalgamate_agree η hG h
  naturality := sorry

/-- Type-`u` fppf sheafification of a Type-`u` presheaf on `Over S`, as the double plus
construction: matching families of presented fppf covers, quotiented by agreement on a
common fppf refinement, applied twice. -/
def sheafifyTypeU {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u) :
    (Over S)ᵒᵖ ⥤ Type u :=
  plusTypeU (plusTypeU F)

/-- The value of Type-`u` fppf sheafification is the double quotient of matching families
by agreement on a common fppf refinement. -/
theorem sheafifyTypeU_obj {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u) (T : (Over S)ᵒᵖ) :
    (sheafifyTypeU F).obj T = (plusTypeU (plusTypeU F)).obj T :=
  sorry

/-- The Type-`u` fppf sheafification of a Type-`u` presheaf is an fppf sheaf. -/
theorem sheafifyTypeU_isSheaf {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (sheafifyTypeU F) :=
  sorry

/-- The unit of Type-`u` fppf sheafification. -/
def toSheafifyTypeU {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u) :
    F ⟶ sheafifyTypeU F :=
  toPlusTypeU F ≫ plusTypeUMap (toPlusTypeU F)

/-- The unit of Type-`u` fppf sheafification factors as the double plus unit. -/
theorem toSheafifyTypeU_eq {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u) :
    toSheafifyTypeU F = toPlusTypeU F ≫ plusTypeUMap (toPlusTypeU F) :=
  sorry

/-- The lift of a morphism into an fppf sheaf through Type-`u` sheafification. -/
def sheafifyTypeULift {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} (η : F ⟶ G)
    (hG : Presheaf.IsSheaf (Scheme.fppfTopology.over S) G) :
    sheafifyTypeU F ⟶ G :=
  plusTypeULift (plusTypeULift η hG) hG

/-- `sheafifyTypeULift` is the double plus lift into an fppf sheaf. -/
theorem sheafifyTypeULift_eq {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} (η : F ⟶ G)
    (hG : Presheaf.IsSheaf (Scheme.fppfTopology.over S) G) :
    sheafifyTypeULift η hG = plusTypeULift (plusTypeULift η hG) hG :=
  sorry

/-- Related points of a pre-relation become equal after composing with an equalizing
morphism into an algebraic space. -/
theorem quotientPresheafDescTo_respects {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) {F : AlgebraicSpace S} (q : yoneda.obj U ⟶ F.functorOfPoints)
    (h_equalizes : yoneda.map P.t ≫ q = yoneda.map P.s ≫ q) {T : (Over S)ᵒᵖ}
    {x y : T.unop ⟶ U} (hxy : P.pointRel T.unop x y) :
    q.app T x = q.app T y :=
  sorry

/-- Descent of a morphism out of `U` along the objectwise quotient of `P`. -/
def quotientPresheafDescTo {S : Scheme.{u}} {U : Over S} (P : PreRelation U)
    {F : AlgebraicSpace S} (q : yoneda.obj U ⟶ F.functorOfPoints)
    (h_equalizes : yoneda.map P.t ≫ q = yoneda.map P.s ≫ q) :
    P.quotientPresheaf ⟶ F.functorOfPoints where
  app T :=
    TypeCat.ofHom <|
      Quot.lift (fun x : T.unop ⟶ U ↦ q.app T x) fun _ _ hxy ↦
        quotientPresheafDescTo_respects P q h_equalizes hxy
  naturality := sorry

/-- The two projections of the normalized relation equalize after composing with the
normalized atlas of `X`. -/
theorem normalizedRelation_equalizes {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    yoneda.map (normalizedRelation X).t ≫
        yoneda.map (overNormalizationTo (finiteComponentsScheme X)) ≫
          finiteComponentsAtlas X =
      yoneda.map (normalizedRelation X).s ≫
        yoneda.map (overNormalizationTo (finiteComponentsScheme X)) ≫
          finiteComponentsAtlas X :=
  sorry

/-- The canonical atlas of the Type-`u` sheafification of the normalized presentation. -/
def normalizationAtlas {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    yoneda.obj (overNormalization (finiteComponentsScheme X)) ⟶
      sheafifyTypeU (normalizedRelation X).quotientPresheaf :=
  (normalizedRelation X).quotientMk ≫
    toSheafifyTypeU (normalizedRelation X).quotientPresheaf

/-- The normalized atlas of `X` is representable, étale, and surjective onto the
Type-`u` sheafification of the quotient presheaf. -/
theorem normalizationAtlas_presheaf_etaleSurjective {S : Scheme.{u}}
    (X : AlgebraicSpace S) [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    (MorphismProperty.over (@AlgebraicGeometry.Etale ⊓ @AlgebraicGeometry.Surjective)).presheaf
      (normalizationAtlas X) :=
  sorry

/-- The absolute normalization `X^ν` of an algebraic space with finitely many irreducible
components on compact opens. -/
def normalization {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] : AlgebraicSpace S :=
  ofEtaleSurjective (sheafifyTypeU_isSheaf (normalizedRelation X).quotientPresheaf)
    (normalizationAtlas X) (normalizationAtlas_presheaf_etaleSurjective X)

/-- The functor of points of `X.normalization` is the Type-`u` fppf sheafification of
the objectwise quotient of the normalized presentation relation. -/
theorem normalization_functorOfPoints {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    X.normalization.functorOfPoints =
      sheafifyTypeU (normalizedRelation X).quotientPresheaf :=
  sorry

/-- The canonical absolute normalization morphism `ν_X : X^ν ⟶ X`. -/
def normalizationTo {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    X.normalization ⟶ X :=
  sheafifyTypeULift
    (quotientPresheafDescTo (normalizedRelation X)
      (yoneda.map (overNormalizationTo (finiteComponentsScheme X)) ≫ finiteComponentsAtlas X)
      (normalizedRelation_equalizes X))
    X.isSheaf

/-- The sheafification unit of the normalized presentation, postcomposed with `ν_X`,
recovers the normalized atlas of `X`. -/
theorem normalizationTo_comp {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    (normalizedRelation X).quotientMk ≫
        toSheafifyTypeU (normalizedRelation X).quotientPresheaf ≫ X.normalizationTo =
      yoneda.map (overNormalizationTo (finiteComponentsScheme X)) ≫ finiteComponentsAtlas X :=
  sorry

/-- The algebraic space over `S` represented by the absolute normalization of the
underlying scheme of `T`. -/
def ofOverSchemeNormalization {S : Scheme.{u}} (T : Over S)
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens T.left] :
    AlgebraicSpace S :=
  ofOver (Over.mk (T.left.normalizationTo ≫ T.hom))

/-- `ofOverSchemeNormalization T` is `ofOver` of the scheme-level absolute
normalization of `T`. -/
theorem ofOverSchemeNormalization_eq {S : Scheme.{u}} (T : Over S)
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens T.left] :
    ofOverSchemeNormalization T =
      ofOver (Over.mk (T.left.normalizationTo ≫ T.hom)) :=
  sorry

/-- The scheme-level absolute normalization morphism of `T`, as a morphism of algebraic
spaces over `S`. -/
def ofOverSchemeNormalizationTo {S : Scheme.{u}} (T : Over S)
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens T.left] :
    ofOverSchemeNormalization T ⟶ ofOver T :=
  ofOverMap (Over.homMk T.left.normalizationTo rfl)

/-- `ofOverSchemeNormalizationTo T` is `ofOverMap` of the scheme-level absolute
normalization morphism of `T`. -/
theorem ofOverSchemeNormalizationTo_eq {S : Scheme.{u}} (T : Over S)
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens T.left] :
    ofOverSchemeNormalizationTo T = ofOverMap (Over.homMk T.left.normalizationTo rfl) :=
  sorry

/-- A morphism of algebraic spaces sends codimension-`0` points to codimension-`0` points. -/
def mapsCodimZero {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop :=
  Set.MapsTo (Points.map f) (codimZeroPoints X) (codimZeroPoints Y)

/-- `mapsCodimZero f` means `Points.map f` sends `codimZeroPoints X` into
`codimZeroPoints Y`. -/
theorem mapsCodimZero_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    mapsCodimZero f ↔
      Set.MapsTo (Points.map f) (codimZeroPoints X) (codimZeroPoints Y) :=
  Iff.rfl

/-- A flat morphism of algebraic spaces sends codimension-`0` points to codimension-`0`
points. -/
theorem mapsCodimZero_of_flat {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Flat f] : mapsCodimZero f :=
  sorry

/-- A smooth morphism of algebraic spaces sends codimension-`0` points to
codimension-`0` points. -/
theorem mapsCodimZero_of_smooth {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Smooth f] : mapsCodimZero f :=
  mapsCodimZero_of_flat f

/-- An étale morphism of algebraic spaces sends codimension-`0` points to
codimension-`0` points. -/
theorem mapsCodimZero_of_etale {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Etale f] : mapsCodimZero f :=
  mapsCodimZero_of_smooth f

/-- A smooth morphism of algebraic spaces pulls the finite-components-on-compact-opens
property back from the target to the source. -/
theorem HasFiniteIrreducibleComponentsOnCompactOpens.of_smooth
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Smooth f]
    [HasFiniteIrreducibleComponentsOnCompactOpens Y] :
    HasFiniteIrreducibleComponentsOnCompactOpens X :=
  HasFiniteIrreducibleComponentsOnCompactOpens.of_flat_locallyOfFiniteType f

/-- An étale morphism of algebraic spaces pulls the finite-components-on-compact-opens
property back from the target to the source. -/
theorem HasFiniteIrreducibleComponentsOnCompactOpens.of_etale
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f]
    [HasFiniteIrreducibleComponentsOnCompactOpens Y] :
    HasFiniteIrreducibleComponentsOnCompactOpens X :=
  HasFiniteIrreducibleComponentsOnCompactOpens.of_smooth f

/-- The unique lift of a generic-point-preserving morphism of schemes over `S` through
absolute normalization exists. -/
theorem existsUnique_overNormalizationMap_of_mapsTo {S : Scheme.{u}} {U V : Over S}
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U.left]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens V.left]
    (g : U ⟶ V)
    (hg : Set.MapsTo g.left (genericPoints U.left) (genericPoints V.left)) :
    ∃! f : overNormalization U ⟶ overNormalization V,
      f ≫ overNormalizationTo V = overNormalizationTo U ≫ g :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
