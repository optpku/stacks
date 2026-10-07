module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Effectivity
public import ReasLib.AlgebraicGeometry.Scheme.Gluing.DoubleAlong.AffineSpace
public import ReasLib.CategoryTheory.Limits.ChosenPullback.Canonical
public import stacks_project.Chap65.Example_65_14_2_Space

/-!
# Doubled-origin base change and non-effective descent

This module records the finite étale base change of the quadratic quotient along `U → S`,
its identification with affine line with doubled origin, the scalar extension to `k'`, and
the non-effective descent datum for schemes along `{Spec(k') → Spec(k)}`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.DescentData

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent

/-- Comparison from relative affine 1-space over `k'` to `Spec(k'[x])`. -/
def affineLineHom (k' : Type u) [Field k'] :
    DoubledOrigin.affineSpace k' 1 ⟶ Spec (CommRingCat.of (Polynomial k')) :=
  (PuncturedAffineSpace.coordinateModelIso (ULift.{u} (Fin 1)) k').hom ≫
    Spec.map (CommRingCat.ofHom (Polynomial.toMvPolynomial (ULift.up (0 : Fin 1))).toRingHom)

/-- `affineLineHom` is the composite of `coordinateModelIso` with `Spec` of `toMvPolynomial`. -/
theorem affineLineHom_eq (k' : Type u) [Field k'] :
    affineLineHom k' =
      (PuncturedAffineSpace.coordinateModelIso (ULift.{u} (Fin 1)) k').hom ≫
        Spec.map
          (CommRingCat.ofHom (Polynomial.toMvPolynomial (ULift.up (0 : Fin 1))).toRingHom) :=
  sorry

/-- The comparison from relative affine 1-space to `Spec(k'[x])` is an isomorphism. -/
theorem isIso_affineLineHom (k' : Type u) [Field k'] : IsIso (affineLineHom k') := sorry

/-- Affine 1-space with doubled origin, as a scheme over `U = Spec(k'[x])`. -/
def doubledOriginOver (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    Over (cover k k').left :=
  Over.mk (DoubledOrigin.fold k' 1 ≫ affineLineHom k')

/-- The structure morphism of `doubledOriginOver` is the fold followed by `affineLineHom`. -/
theorem doubledOriginOver_hom (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    (doubledOriginOver k k').hom = DoubledOrigin.fold k' 1 ≫ affineLineHom k' := sorry

/-- The base change of `X` along `U → S`, as an fppf sheaf on schemes over `U`. -/
def baseChangeSheaf (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    Sheaf (Scheme.fppfTopology.over (cover k k').left) (Type (u + 1)) :=
  ((Over.map (cover k k').hom).sheafPushforwardContinuous (Type (u + 1))
      (Scheme.fppfTopology.over (cover k k').left) (Scheme.fppfTopology.over (base k))).obj
    (sheafOfPoints k k' hdeg)

/-- `baseChangeSheaf` is the sheaf pushforward of `sheafOfPoints` along `Over.map (U → S)`. -/
theorem baseChangeSheaf_eq (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    baseChangeSheaf k k' hdeg =
      ((Over.map (cover k k').hom).sheafPushforwardContinuous (Type (u + 1))
          (Scheme.fppfTopology.over (cover k k').left) (Scheme.fppfTopology.over (base k))).obj
        (sheafOfPoints k k' hdeg) := sorry

/-- After base change along `U → S`, the quotient becomes the affine line with `0` doubled. -/
theorem iso_doubledOrigin (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    Nonempty
      (baseChangeSheaf k k' hdeg ≅
        (Scheme.fppfTopology.over (cover k k').left).uliftYoneda.{u + 1}.obj
          (doubledOriginOver k k')) :=
  sorry

/-- The ground scheme `Spec(k)`. -/
abbrev ground (k : Type u) [Field k] : Scheme.{u} := Spec (CommRingCat.of k)

/-- The ground scheme is the spectrum of `k`. -/
theorem ground_eq (k : Type u) [Field k] : ground k = Spec (CommRingCat.of k) := sorry

/-- The covering morphism `Spec(k') → Spec(k)`. -/
def groundCover (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    Spec (CommRingCat.of k') ⟶ ground k :=
  Spec.map (CommRingCat.ofHom (algebraMap k k'))

/-- The covering morphism is `Spec` of the algebra map. -/
theorem groundCover_eq (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    groundCover k k' = Spec.map (CommRingCat.ofHom (algebraMap k k')) := sorry

/-- `Spec(k') → Spec(k)` is étale. -/
theorem etale_groundCover (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2) :
    Etale (groundCover k k') := sorry

/-- `Spec(k') → Spec(k)` is finite. -/
theorem isFinite_groundCover (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2) :
    IsFinite (groundCover k k') := sorry

/-- `Spec(k') → Spec(k)` is surjective. -/
theorem surjective_groundCover (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2) :
    Surjective (groundCover k k') := sorry

/-- Affine 1-space with doubled origin, as a scheme over `Spec(k')`. -/
def descentObject (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    Over (Spec (CommRingCat.of k')) :=
  Over.mk (DoubledOrigin.fold k' 1 ≫ PuncturedAffineSpace.toBase (ULift.{u} (Fin 1)) k')

/-- The structure morphism of `descentObject` is the fold to affine 1-space over `k'`. -/
theorem descentObject_hom (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    (descentObject k k').hom =
      DoubledOrigin.fold k' 1 ≫ PuncturedAffineSpace.toBase (ULift.{u} (Fin 1)) k' :=
  sorry

/-- Compatibility of the swapped charts on the punctured overlap. -/
theorem galComparison_compatible (k' : Type u) [Field k'] :
    (PuncturedAffineSpace.puncturedOpen (ULift.{u} (Fin 1)) k').ι ≫
        DoubledOrigin.chartMap k' 1 (1 - 0) =
      (PuncturedAffineSpace.puncturedOpen (ULift.{u} (Fin 1)) k').ι ≫
        DoubledOrigin.chartMap k' 1 (1 - 1) := sorry

/-- The swap of the two origins on affine 1-space with doubled origin. -/
def galComparison (k' : Type u) [Field k'] :
    DoubledOrigin.scheme k' 1 ⟶ DoubledOrigin.scheme k' 1 :=
  Scheme.DoubleAlong.desc (PuncturedAffineSpace.puncturedOpen (ULift.{u} (Fin 1)) k')
    (fun i ↦ DoubledOrigin.chartMap k' 1 (1 - i)) (galComparison_compatible k')

/-- The Galois comparison swaps the two canonical charts. -/
theorem galComparison_chartMap (k' : Type u) [Field k'] (i : Fin 2) :
    DoubledOrigin.chartMap k' 1 i ≫ galComparison k' =
      DoubledOrigin.chartMap k' 1 (1 - i) := sorry

/-- The chosen self-overlap `Spec(k') ×_k Spec(k')` of the covering morphism. -/
def groundOverlap (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    ChosenPullback (groundCover k k') (groundCover k k') :=
  ChosenPullback.ofHasPullback (groundCover k k') (groundCover k k')

/-- `groundOverlap` is the canonical pullback of `groundCover` with itself. -/
theorem groundOverlap_eq (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    groundOverlap k k' = ChosenPullback.ofHasPullback (groundCover k k') (groundCover k k') :=
  sorry

/-- The two projections of `groundOverlap` agree after composing with `groundCover`. -/
theorem identityComponent_w (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    𝟙 (Spec (CommRingCat.of k')) ≫ groundCover k k' =
      𝟙 (Spec (CommRingCat.of k')) ≫ groundCover k k' := sorry

/-- The identity component of `Spec(k') ×_k Spec(k')`, as the diagonal. -/
def identityComponent (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    Spec (CommRingCat.of k') ⟶ (groundOverlap k k').pullback :=
  pullback.lift (𝟙 _) (𝟙 _) (identityComponent_w k k')

/-- The identity component projects to the identity on each factor. -/
theorem identityComponent_fst (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    identityComponent k k' ≫ (groundOverlap k k').p₁ = 𝟙 _ := sorry

/-- The identity component projects to the identity on the second factor. -/
theorem identityComponent_snd (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    identityComponent k k' ≫ (groundOverlap k k').p₂ = 𝟙 _ := sorry

/-- The automorphism of `Spec(k')` induced by `galConj`. -/
def galBaseAut (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k') :=
  Spec.map (CommRingCat.ofHom (galConj k k' hdeg).toRingHom)

/-- `galBaseAut` is `Spec` of `galConj`. -/
theorem galBaseAut_eq (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    galBaseAut k k' hdeg = Spec.map (CommRingCat.ofHom (galConj k k' hdeg).toRingHom) := sorry

/-- The graph of `galConj` lies over `Spec(k)`. -/
theorem galComponent_w (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    𝟙 (Spec (CommRingCat.of k')) ≫ groundCover k k' =
      galBaseAut k k' hdeg ≫ groundCover k k' := sorry

/-- The non-identity component of `Spec(k') ×_k Spec(k')`, as the graph of `galConj`. -/
def galComponent (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    Spec (CommRingCat.of k') ⟶ (groundOverlap k k').pullback :=
  pullback.lift (𝟙 _) (galBaseAut k k' hdeg) (galComponent_w k k' hdeg)

/-- The non-identity component projects to the identity on the first factor. -/
theorem galComponent_fst (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    galComponent k k' hdeg ≫ (groundOverlap k k').p₁ = 𝟙 _ := sorry

/-- The non-identity component projects to `galBaseAut` on the second factor. -/
theorem galComponent_snd (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    galComponent k k' hdeg ≫ (groundOverlap k k').p₂ = galBaseAut k k' hdeg := sorry

/-- The chosen triple overlap of `groundCover` with itself. -/
def groundTripleMiddle (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    ChosenPullback (groundOverlap k k').p₂ (groundOverlap k k').p₁ :=
  ChosenPullback.ofHasPullback (groundOverlap k k').p₂ (groundOverlap k k').p₁

/-- The first wide projection from the triple overlap. -/
def groundTripleFirst (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    (groundTripleMiddle k k').pullback ⟶ Spec (CommRingCat.of k') :=
  (groundTripleMiddle k k').p₁ ≫ (groundOverlap k k').p₁

/-- The third wide projection from the triple overlap. -/
def groundTripleThird (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    (groundTripleMiddle k k').pullback ⟶ Spec (CommRingCat.of k') :=
  (groundTripleMiddle k k').p₂ ≫ (groundOverlap k k').p₂

/-- The first and third triple-overlap projections agree over `Spec(k)`. -/
theorem groundTripleLift_w (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    groundTripleFirst k k' ≫ groundCover k k' =
      groundTripleThird k k' ≫ groundCover k k' := sorry

/-- The map from the triple overlap to the pairwise overlap. -/
def groundTripleLift (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    (groundTripleMiddle k k').pullback ⟶ (groundOverlap k k').pullback :=
  (groundOverlap k k').isPullback.lift (groundTripleFirst k k') (groundTripleThird k k')
    (groundTripleLift_w k k')

/-- The triple-to-pair map has the prescribed first projection. -/
theorem groundTripleLift_p₁ (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    groundTripleLift k k' ≫ (groundOverlap k k').p₁ = groundTripleFirst k k' := sorry

/-- The triple-to-pair map has the prescribed second projection. -/
theorem groundTripleLift_p₂ (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    groundTripleLift k k' ≫ (groundOverlap k k').p₂ = groundTripleThird k k' := sorry

/-- The triple-to-pair map is compatible with the common map to `Spec(k)`. -/
theorem groundTripleLift_p (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    groundTripleLift k k' ≫ (groundOverlap k k').p =
      groundTripleFirst k k' ≫ groundCover k k' := sorry

/-- The first displayed projection of the triple overlap is the chosen one. -/
theorem groundTriple_hp₁ (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    (groundTripleMiddle k k').p₁ ≫ (groundOverlap k k').p₁ = groundTripleFirst k k' := sorry

/-- The third displayed projection of the triple overlap is the chosen one. -/
theorem groundTriple_hp₃ (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    (groundTripleMiddle k k').p₂ ≫ (groundOverlap k k').p₂ = groundTripleThird k k' := sorry

/-- The chosen triple overlap of the singleton covering family. -/
def groundTriple (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    ChosenPullback₃ (groundOverlap k k') (groundOverlap k k') (groundOverlap k k') where
  chosenPullback := groundTripleMiddle k k'
  p := groundTripleFirst k k' ≫ groundCover k k'
  p₁ := groundTripleFirst k k'
  p₃ := groundTripleThird k k'
  l :=
    { f := groundTripleLift k k'
      f_p₁ := groundTripleLift_p₁ k k'
      f_p₂ := groundTripleLift_p₂ k k'
      f_p := groundTripleLift_p k k' }
  hp₁ := groundTriple_hp₁ k k'
  hp₃ := groundTriple_hp₃ k k'

/-- `groundTriple` is assembled from the canonical middle pullback of `groundOverlap`. -/
theorem groundTriple_chosenPullback (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    (groundTriple k k').chosenPullback = groundTripleMiddle k k' := sorry

/-- The Galois action on affine 1-space over `k'`, covering `galBaseAut`. -/
def galActAffineLine (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    DoubledOrigin.affineSpace k' 1 ⟶ DoubledOrigin.affineSpace k' 1 :=
  (PuncturedAffineSpace.coordinateModelIso (ULift.{u} (Fin 1)) k').hom ≫
    Spec.map (CommRingCat.ofHom (MvPolynomial.map (galConj k k' hdeg).toRingHom)) ≫
      (PuncturedAffineSpace.coordinateModelIso (ULift.{u} (Fin 1)) k').inv

/-- `galActAffineLine` is conjugation of `MvPolynomial.map galConj` by `coordinateModelIso`. -/
theorem galActAffineLine_eq (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    galActAffineLine k k' hdeg =
      (PuncturedAffineSpace.coordinateModelIso (ULift.{u} (Fin 1)) k').hom ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.map (galConj k k' hdeg).toRingHom)) ≫
          (PuncturedAffineSpace.coordinateModelIso (ULift.{u} (Fin 1)) k').inv := sorry

/-- Compatibility of the Galois origin-swap on the punctured overlap. -/
theorem galActSwap_compatible (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    (PuncturedAffineSpace.puncturedOpen (ULift.{u} (Fin 1)) k').ι ≫
        galActAffineLine k k' hdeg ≫ DoubledOrigin.chartMap k' 1 (1 - 0) =
      (PuncturedAffineSpace.puncturedOpen (ULift.{u} (Fin 1)) k').ι ≫
        galActAffineLine k k' hdeg ≫ DoubledOrigin.chartMap k' 1 (1 - 1) := sorry

/-- The Galois origin-swap of affine 1-space with doubled origin: apply `galConj` and swap the
two origins. -/
def galActSwap (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    DoubledOrigin.scheme k' 1 ⟶ DoubledOrigin.scheme k' 1 :=
  Scheme.DoubleAlong.desc (PuncturedAffineSpace.puncturedOpen (ULift.{u} (Fin 1)) k')
    (fun i ↦ galActAffineLine k k' hdeg ≫ DoubledOrigin.chartMap k' 1 (1 - i))
    (galActSwap_compatible k k' hdeg)

/-- `galActSwap` restricts to Galois action followed by the opposite chart. -/
theorem galActSwap_chartMap (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) (i : Fin 2) :
    DoubledOrigin.chartMap k' 1 i ≫ galActSwap k k' hdeg =
      galActAffineLine k k' hdeg ≫ DoubledOrigin.chartMap k' 1 (1 - i) := sorry

/-- The identity-component section of the `p₁`-pullback of the descent object. -/
theorem identitySection_w (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    𝟙 (DoubledOrigin.scheme k' 1) ≫ (descentObject k k').hom =
      ((descentObject k k').hom ≫ identityComponent k k') ≫ (groundOverlap k k').p₁ := sorry

/-- The identity-component open of the `p₁`-pullback of the descent object. -/
def identitySection (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    DoubledOrigin.scheme k' 1 ⟶
      ((Over.pullback (groundOverlap k k').p₁).obj (descentObject k k')).left :=
  pullback.lift (𝟙 _) ((descentObject k k').hom ≫ identityComponent k k')
    (identitySection_w k k')

/-- The identity-component section of the `p₂`-pullback of the descent object. -/
theorem identityToCodomain_w (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    𝟙 (DoubledOrigin.scheme k' 1) ≫ (descentObject k k').hom =
      ((descentObject k k').hom ≫ identityComponent k k') ≫ (groundOverlap k k').p₂ := sorry

/-- The identity comparison on the identity component. -/
def identityToCodomain (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    DoubledOrigin.scheme k' 1 ⟶
      ((Over.pullback (groundOverlap k k').p₂).obj (descentObject k k')).left :=
  pullback.lift (𝟙 _) ((descentObject k k').hom ≫ identityComponent k k')
    (identityToCodomain_w k k')

/-- The non-identity-component section of the `p₁`-pullback of the descent object. -/
theorem galSection_w (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    𝟙 (DoubledOrigin.scheme k' 1) ≫ (descentObject k k').hom =
      ((descentObject k k').hom ≫ galComponent k k' hdeg) ≫ (groundOverlap k k').p₁ := sorry

/-- The non-identity-component open of the `p₁`-pullback of the descent object. -/
def galSection (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    DoubledOrigin.scheme k' 1 ⟶
      ((Over.pullback (groundOverlap k k').p₁).obj (descentObject k k')).left :=
  pullback.lift (𝟙 _) ((descentObject k k').hom ≫ galComponent k k' hdeg) (galSection_w k k' hdeg)

/-- The origin-swapping Galois comparison covers `galBaseAut`. -/
theorem galToCodomain_w (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    galActSwap k k' hdeg ≫ (descentObject k k').hom =
      ((descentObject k k').hom ≫ galComponent k k' hdeg) ≫ (groundOverlap k k').p₂ := sorry

/-- The origin-swapping comparison on the non-identity component. -/
def galToCodomain (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    DoubledOrigin.scheme k' 1 ⟶
      ((Over.pullback (groundOverlap k k').p₂).obj (descentObject k k')).left :=
  pullback.lift (galActSwap k k' hdeg) ((descentObject k k').hom ≫ galComponent k k' hdeg)
    (galToCodomain_w k k' hdeg)

/-- The two components cover the `p₁`-pullback of the descent object. -/
theorem descentComparisonCover_covers (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2)
    (x : ((Over.pullback (groundOverlap k k').p₁).obj (descentObject k k')).left) :
    ∃ j : Fin 2,
      ∃ y,
        (if j = 0 then identitySection k k' else galSection k k' hdeg) y = x := sorry

/-- Each component inclusion of the comparison cover is an open immersion. -/
theorem descentComparisonCover_isOpenImmersion (k k' : Type u) [Field k] [Field k']
    [Algebra k k'] [IsGalois k k'] (hdeg : Module.finrank k k' = 2) (j : Fin 2) :
    IsOpenImmersion (if j = 0 then identitySection k k' else galSection k k' hdeg) := sorry

/-- The open cover of the `p₁`-pullback by the identity and `galConj` components. -/
def descentComparisonCover (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    Scheme.OpenCover ((Over.pullback (groundOverlap k k').p₁).obj (descentObject k k')).left :=
  Scheme.Cover.mkOfCovers (Fin 2) (fun _ ↦ DoubledOrigin.scheme k' 1)
    (fun j ↦ if j = 0 then identitySection k k' else galSection k k' hdeg)
    (descentComparisonCover_covers k k' hdeg)
    (descentComparisonCover_isOpenImmersion k k' hdeg)

/-- The local comparison maps on the two components of `descentComparisonCover`. -/
def descentComparisonOnCover (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) (j : Fin 2) :
    DoubledOrigin.scheme k' 1 ⟶
      ((Over.pullback (groundOverlap k k').p₂).obj (descentObject k k')).left :=
  if j = 0 then identityToCodomain k k' else galToCodomain k k' hdeg

/-- The local comparison maps agree on overlaps. -/
theorem descentComparisonOnCover_compat (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2) :
    ∀ j ℓ,
      pullback.fst ((descentComparisonCover k k' hdeg).f j)
          ((descentComparisonCover k k' hdeg).f ℓ) ≫
        descentComparisonOnCover k k' hdeg j =
      pullback.snd ((descentComparisonCover k k' hdeg).f j)
          ((descentComparisonCover k k' hdeg).f ℓ) ≫
        descentComparisonOnCover k k' hdeg ℓ := sorry

/-- The underlying scheme morphism of the pairwise descent comparison. -/
def descentComparisonLeft (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    ((Over.pullback (groundOverlap k k').p₁).obj (descentObject k k')).left ⟶
      ((Over.pullback (groundOverlap k k').p₂).obj (descentObject k k')).left :=
  Scheme.Cover.glueMorphisms (descentComparisonCover k k' hdeg)
    (descentComparisonOnCover k k' hdeg) (descentComparisonOnCover_compat k k' hdeg)

/-- The glued comparison is a morphism over the overlap. -/
theorem descentComparison_w (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    descentComparisonLeft k k' hdeg ≫
        ((Over.pullback (groundOverlap k k').p₂).obj (descentObject k k')).hom =
      ((Over.pullback (groundOverlap k k').p₁).obj (descentObject k k')).hom := sorry

/-- Pairwise comparison of the doubled-origin object over `Spec(k') ×_k Spec(k')`: identity on
the identity component, and the Galois origin-swap on the non-identity component. -/
def descentComparison (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    (Over.pullback (groundOverlap k k').p₁).obj (descentObject k k') ⟶
      (Over.pullback (groundOverlap k k').p₂).obj (descentObject k k') :=
  Over.homMk (descentComparisonLeft k k' hdeg) (descentComparison_w k k' hdeg)

/-- The underlying scheme morphism of `descentComparison` is `descentComparisonLeft`. -/
theorem descentComparison_left (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    (descentComparison k k' hdeg).left = descentComparisonLeft k k' hdeg := sorry

/-- The chosen presentation of the non-effective descent datum along `{Spec(k') → Spec(k)}`. -/
def descentDataChosen (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    Chosen (fun _ : PUnit.{1} ↦ Spec (CommRingCat.of k')) (fun _ ↦ groundCover k k')
      (fun _ _ ↦ groundOverlap k k') (fun _ _ _ ↦ groundTriple k k') where
  obj _ := descentObject k k'
  hom _ _ := descentComparison k k' hdeg
  pullHom'_hom_self := sorry
  pullHom'_hom_comp := sorry

/-- The unique component of `descentDataChosen` is the doubled-origin scheme over `Spec(k')`. -/
theorem descentDataChosen_obj (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) (i : PUnit.{1}) :
    (descentDataChosen k k' hdeg).obj i = descentObject k k' := sorry

/-- The descent datum for schemes along `{Spec(k') → Spec(k)}` with object the affine line
with `0` doubled and pairwise comparison the Galois origin-swap on the non-identity
component of `Spec(k') ×_k Spec(k')`. -/
def descentData (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    DescentData (fun _ : PUnit.{1} ↦ Spec (CommRingCat.of k')) (fun _ ↦ groundCover k k') :=
  (Chosen.equivalence (fun _ : PUnit.{1} ↦ Spec (CommRingCat.of k'))
      (fun _ ↦ groundCover k k') (fun _ _ ↦ groundOverlap k k')
      (fun _ _ _ ↦ groundTriple k k')).functor.obj
    (descentDataChosen k k' hdeg)

/-- `descentData` is the image of `descentDataChosen` under the chosen-to-canonical
equivalence. -/
theorem descentData_eq (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    descentData k k' hdeg =
      (Chosen.equivalence (fun _ : PUnit.{1} ↦ Spec (CommRingCat.of k'))
          (fun _ ↦ groundCover k k') (fun _ _ ↦ groundOverlap k k')
          (fun _ _ _ ↦ groundTriple k k')).functor.obj
        (descentDataChosen k k' hdeg) := sorry

/-- The unique component of `descentData` is the doubled-origin scheme over `Spec(k')`. -/
theorem descentData_obj (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) (i : PUnit.{1}) :
    (descentData k k' hdeg).obj i = descentObject k k' := sorry

/-- The descent datum along `{Spec(k') → Spec(k)}` is not effective. -/
theorem not_isEffective_descentData (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2) :
    ¬ (descentData k k' hdeg).IsEffective := sorry

/-- Non-effectivity means the datum is not isomorphic to the canonical pullback of any scheme
over `Spec(k)`. -/
theorem not_isEffective_descentData_iff (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2) :
    ¬ ∃ U : Over (ground k),
        Nonempty
          (ofObj (fun _ : PUnit.{1} ↦ Spec (CommRingCat.of k')) (fun _ ↦ groundCover k k') U ≅
            descentData k k' hdeg) := sorry

/-- Viewing `X` over `Spec(k)` via `S → Spec(k)`. -/
def toGround (k : Type u) [Field k] : base k ⟶ ground k :=
  Spec.map (CommRingCat.ofHom Polynomial.C)

/-- The morphism `S → Spec(k)` is `Spec` of the constant-coefficient map. -/
theorem toGround_eq (k : Type u) [Field k] :
    toGround k = Spec.map (CommRingCat.ofHom Polynomial.C) := sorry

/-- The scalar extension of `X` along `Spec(k') → Spec(k)`, as an fppf sheaf over `Spec(k')`. -/
def sheafOverGround (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    Sheaf (Scheme.fppfTopology.over (ground k)) (Type (u + 1)) :=
  ((Over.map (toGround k)).sheafPullback (Type (u + 1)) (Scheme.fppfTopology.over (base k))
      (Scheme.fppfTopology.over (ground k))).obj
    (sheafOfPoints k k' hdeg)

/-- `sheafOverGround` is `sheafOfPoints` extended along `S → Spec(k)`. -/
theorem sheafOverGround_eq (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    sheafOverGround k k' hdeg =
      ((Over.map (toGround k)).sheafPullback (Type (u + 1)) (Scheme.fppfTopology.over (base k))
          (Scheme.fppfTopology.over (ground k))).obj
        (sheafOfPoints k k' hdeg) := sorry

/-- The scalar extension of `X` along `Spec(k') → Spec(k)`, as an fppf sheaf over `Spec(k')`. -/
def scalarExtensionSheaf (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    Sheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of k'))) (Type (u + 1)) :=
  ((Over.map (groundCover k k')).sheafPushforwardContinuous (Type (u + 1))
      (Scheme.fppfTopology.over (Spec (CommRingCat.of k')))
      (Scheme.fppfTopology.over (ground k))).obj
    (sheafOverGround k k' hdeg)

/-- `scalarExtensionSheaf` is the sheaf pushforward of `sheafOverGround` to `Spec(k')`. -/
theorem scalarExtensionSheaf_eq (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2) :
    scalarExtensionSheaf k k' hdeg =
      ((Over.map (groundCover k k')).sheafPushforwardContinuous (Type (u + 1))
          (Scheme.fppfTopology.over (Spec (CommRingCat.of k')))
          (Scheme.fppfTopology.over (ground k))).obj
        (sheafOverGround k k' hdeg) :=
  sorry

/-- After scalar extension to `k'`, the space becomes representable (a scheme). -/
theorem scalarExtension_isRepresentable (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2) :
    ∃ T : Over (Spec (CommRingCat.of k')),
      Nonempty
        (scalarExtensionSheaf k k' hdeg ≅
          (Scheme.fppfTopology.over (Spec (CommRingCat.of k'))).uliftYoneda.{u + 1}.obj T) :=
  sorry

/-- Viewed over `Spec(k)`, the space `X` is still not representable by a scheme. -/
theorem not_isRepresentable_overGround (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2) :
    ¬ ∃ T : Over (ground k),
        Nonempty
          (sheafOverGround k k' hdeg ≅
            (Scheme.fppfTopology.over (ground k)).uliftYoneda.{u + 1}.obj T) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent
