/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
public import ReasLib.AlgebraicGeometry.GroupScheme
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Action
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Stabilizer
public import ReasLib.AlgebraicGeometry.RootsOfUnity.GroupScheme
public import ReasLib.CategoryTheory.Fibered.Groupoids.GerbeMorphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.SmallFunctoriality
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Reduced
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicStack.WeightedInfiniteAffine.Action

/-!
# Gerbe strata of the weighted infinite quotient stack

This module indexes the reduced locally closed strata of `[U / 𝔾ₘ]` by `ℕ ∪ {∞}`,
realizes each stratum as the quotient stack of the restricted `𝔾ₘ`-action on the
corresponding invariant locus, and records the gerbe, partition, and coarseness properties.
-/

@[expose] public section

set_option backward.privateInPublic true

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Limits
open AlgebraicGeometry.AlgebraicStack AlgebraicGeometry.Groupoids.Hom
open AlgebraicGeometry.GroupoidAlgebraicSpace
open FiberedCategoryOver.Groupoids.Hom
open CartesianMonoidalCategory MonoidalCategory
open scoped AlgebraicGeometry Bicategory CategoryTheory.MonObj MonoidalLeftAction

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.WeightedInfiniteAffine

/-- The index set `ℕ ∪ {∞}` of the weighted gerbe stratification. -/
inductive StratumIndex where
  /-- Finite index `i` for the stratum `𝒳_i`. -/
  | ofNat (i : ℕ)
  /-- The infinite index for the origin stratum `𝒳_∞`. -/
  | inf

/-- The vanishing ideal `(x_0, …, x_{i-1})` of the first `i` coordinates. -/
def vanishingIdeal (k : Type u) [Field k] (i : ℕ) : Ideal (coordRing k) :=
  Ideal.span (Set.image (MvPolynomial.X : ℕ → coordRing k) (Set.Iio i))

/-- The closed subscheme ring `k[x_j | j : ℕ] / (x_0, …, x_{i-1})`. -/
abbrev finiteClosedRing (k : Type u) [Field k] (i : ℕ) : Type u :=
  coordRing k ⧸ vanishingIdeal k i

/-- The locally closed stratum ring of `𝒳_i`, obtained by inverting the image of `x_i`. -/
abbrev finiteLocusRing (k : Type u) [Field k] (i : ℕ) : Type u :=
  Localization.Away (Ideal.Quotient.mk (vanishingIdeal k i) (MvPolynomial.X i))

/-- The structure map from `k` to the finite-stratum ring. -/
def finiteLocusAlgebraMap (k : Type u) [Field k] (i : ℕ) :
    k →+* finiteLocusRing k i :=
  algebraMap k (finiteLocusRing k i)

/-- The canonical map from the coordinate ring to the finite-stratum ring. -/
def finiteLocusFromCoord (k : Type u) [Field k] (i : ℕ) :
    coordRing k →+* finiteLocusRing k i :=
  algebraMap (coordRing k) (finiteLocusRing k i)

/-- The locally closed locus of `𝒳_i` as a scheme over `Spec k`. -/
def finiteLocus (k : Type u) [Field k] (i : ℕ) : Over (base k) :=
  OverSpec.affine (CommRingCat.ofHom (finiteLocusAlgebraMap k i))

/-- The underlying scheme of `finiteLocus k i` is `Spec` of the inverted quotient. -/
theorem finiteLocus_left (k : Type u) [Field k] (i : ℕ) :
    (finiteLocus k i).left = Spec (CommRingCat.of (finiteLocusRing k i)) := sorry

/-- Compatibility of `finiteLocusFromCoord` with the maps from `k`. -/
private theorem finiteLocusι_w (k : Type u) [Field k] (i : ℕ) :
    Spec.map (CommRingCat.ofHom (finiteLocusFromCoord k i)) ≫ (affineSpace k).hom =
      (finiteLocus k i).hom := sorry

/-- The locally closed immersion of the `𝒳_i` locus into infinite affine space. -/
def finiteLocusι (k : Type u) [Field k] (i : ℕ) : finiteLocus k i ⟶ affineSpace k :=
  Over.homMk (Spec.map (CommRingCat.ofHom (finiteLocusFromCoord k i)))
    (finiteLocusι_w k i)

/-- The underlying scheme map of `finiteLocusι` is `Spec` of `finiteLocusFromCoord`. -/
theorem finiteLocusι_left (k : Type u) [Field k] (i : ℕ) :
    (finiteLocusι k i).left = Spec.map (CommRingCat.ofHom (finiteLocusFromCoord k i)) := sorry

/-- The vanishing ideal of all coordinates, cutting out the origin. -/
def infinityIdeal (k : Type u) [Field k] : Ideal (coordRing k) :=
  Ideal.span (Set.range (MvPolynomial.X : ℕ → coordRing k))

/-- The origin ring `k[x_i | i : ℕ] / (x_i | i : ℕ)`. -/
abbrev infinityLocusRing (k : Type u) [Field k] : Type u :=
  coordRing k ⧸ infinityIdeal k

/-- The structure map from `k` to the origin ring. -/
def infinityLocusAlgebraMap (k : Type u) [Field k] : k →+* infinityLocusRing k :=
  algebraMap k (infinityLocusRing k)

/-- The origin locus `𝒳_∞` as a scheme over `Spec k`. -/
def infinityLocus (k : Type u) [Field k] : Over (base k) :=
  OverSpec.affine (CommRingCat.ofHom (infinityLocusAlgebraMap k))

/-- The underlying scheme of `infinityLocus k` is `Spec` of the origin ring. -/
theorem infinityLocus_left (k : Type u) [Field k] :
    (infinityLocus k).left = Spec (CommRingCat.of (infinityLocusRing k)) := sorry

/-- Compatibility of the origin closed immersion with the maps from `k`. -/
private theorem infinityLocusι_w (k : Type u) [Field k] :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (infinityIdeal k))) ≫
        (affineSpace k).hom =
      (infinityLocus k).hom := sorry

/-- The closed immersion of the origin into infinite affine space. -/
def infinityLocusι (k : Type u) [Field k] : infinityLocus k ⟶ affineSpace k :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (infinityIdeal k))))
    (infinityLocusι_w k)

/-- The underlying scheme map of `infinityLocusι` is `Spec` of the quotient map. -/
theorem infinityLocusι_left (k : Type u) [Field k] :
    (infinityLocusι k).left =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (infinityIdeal k))) := sorry

/-- The representing `𝔾ₘ`-invariant locus of a stratum, as a scheme over `Spec k`. -/
def locus (k : Type u) [Field k] (i : StratumIndex) : Over (base k) :=
  match i with
  | StratumIndex.ofNat n => finiteLocus k n
  | StratumIndex.inf => infinityLocus k

/-- The locally closed immersion of a stratum locus into infinite affine space. -/
def locusι (k : Type u) [Field k] (i : StratumIndex) : locus k i ⟶ affineSpace k :=
  match i with
  | StratumIndex.ofNat n => finiteLocusι k n
  | StratumIndex.inf => infinityLocusι k

/-- `locus` on a finite index is `finiteLocus`. -/
theorem locus_finite (k : Type u) [Field k] (i : ℕ) :
    locus k (StratumIndex.ofNat i) = finiteLocus k i := sorry

/-- `locus` at infinity is `infinityLocus`. -/
theorem locus_infinity (k : Type u) [Field k] :
    locus k StratumIndex.inf = infinityLocus k := sorry

/-- On the locus of `𝒳_i`, the coordinate `x_i` is a unit. -/
theorem finiteLocus_X_isUnit (k : Type u) [Field k]
    (i : ℕ) : IsUnit (finiteLocusFromCoord k i (MvPolynomial.X i)) := sorry

/-- On the locus of `𝒳_i`, the coordinates `x_0, …, x_{i-1}` vanish. -/
theorem finiteLocus_X_eq_zero (k : Type u) [Field k]
    (i : ℕ) (j : ℕ) (hj : j < i) : finiteLocusFromCoord k i (MvPolynomial.X j) = 0 := sorry

/-- The infinite stratum `𝒳_∞` is cut out on `U` by the vanishing of every `x_j`. -/
theorem infinityLocus_X_eq_zero (k : Type u) [Field k] :
    ∀ j : ℕ, Ideal.Quotient.mk (infinityIdeal k) (MvPolynomial.X j) = 0 := sorry

/-- Each finite stratum locus is a reduced scheme. -/
instance instIsReducedFiniteLocus (k : Type u) [Field k] (i : ℕ) :
    AlgebraicGeometry.IsReduced (finiteLocus k i).left := sorry

/-- The origin locus is a reduced scheme. -/
instance instIsReducedInfinityLocus (k : Type u) [Field k] :
    AlgebraicGeometry.IsReduced (infinityLocus k).left := sorry

/-- The representing locus of every stratum is a reduced scheme. -/
instance instIsReducedLocus (k : Type u) [Field k] (i : StratumIndex) :
    AlgebraicGeometry.IsReduced (locus k i).left := sorry

/-- The domain `𝔾ₘ[Spec k] ×_Spec k Z` of the restricted weighted action on a stratum locus. -/
def restrictedActionDomain (k : Type u) [Field k] (i : StratumIndex) : Over (base k) :=
  (𝔾ₘ[base k]).X ⊗ locus k i

/-- The unit pulled back from `𝔾ₘ[Spec k]` along the first projection of the restricted domain. -/
def restrictedActionDomainUnit (k : Type u) [Field k] (i : StratumIndex) :
    Γ((restrictedActionDomain k i).left, ⊤)ˣ :=
  MultiplicativeGroup.baseChangeHomEquiv (base k) (restrictedActionDomain k i)
    (fst (𝔾ₘ[base k]).X (locus k i))

/-- Coordinates of infinite affine space pulled back to `𝔾ₘ × locus`. -/
def restrictedActionDomainCoord (k : Type u) [Field k] (i : StratumIndex) :
    coordRing k →+* Γ((restrictedActionDomain k i).left, ⊤) :=
  (Scheme.homToSpecGlobalSectionsEquiv (restrictedActionDomain k i).left
      (CommRingCat.of (coordRing k))
      ((snd (𝔾ₘ[base k]).X (locus k i)).left ≫ (locusι k i).left)).hom

/-- The ring map `k → Γ(𝔾ₘ × locus, ⊤)` induced by the structure morphism. -/
def restrictedActionDomainBase (k : Type u) [Field k] (i : StratumIndex) :
    k →+* Γ((restrictedActionDomain k i).left, ⊤) :=
  (Scheme.homToSpecGlobalSectionsEquiv (restrictedActionDomain k i).left (CommRingCat.of k)
      (restrictedActionDomain k i).hom).hom

/-- The weighted coaction on coordinates, pulled back to `𝔾ₘ × locus`. -/
def restrictedActionSectionsFromCoord (k : Type u) [Field k] (p : ℕ) (i : StratumIndex) :
    coordRing k →+* Γ((restrictedActionDomain k i).left, ⊤) :=
  MvPolynomial.eval₂Hom (restrictedActionDomainBase k i) fun j ↦
    ((restrictedActionDomainUnit k i ^ p ^ j :
        Γ((restrictedActionDomain k i).left, ⊤)ˣ) :
      Γ((restrictedActionDomain k i).left, ⊤)) *
      restrictedActionDomainCoord k i (MvPolynomial.X j)

/-- The pulled-back coaction vanishes on `(x_0, …, x_{i-1})`. -/
private theorem restrictedActionSectionsFromCoord_vanishingIdeal (k : Type u) [Field k] (p i : ℕ)
    (f : coordRing k) (hf : f ∈ vanishingIdeal k i) :
    restrictedActionSectionsFromCoord k p (StratumIndex.ofNat i) f = 0 := sorry

/-- The pulled-back coaction vanishes on every coordinate at the origin. -/
private theorem restrictedActionSectionsFromCoord_infinityIdeal (k : Type u) [Field k] (p : ℕ)
    (f : coordRing k) (hf : f ∈ infinityIdeal k) :
    restrictedActionSectionsFromCoord k p StratumIndex.inf f = 0 := sorry

/-- The weighted coaction on the closed subscheme ring of `𝒳_i`. -/
def finiteClosedActionSections (k : Type u) [Field k] (p i : ℕ) :
    finiteClosedRing k i →+* Γ((restrictedActionDomain k (StratumIndex.ofNat i)).left, ⊤) :=
  Ideal.Quotient.lift (vanishingIdeal k i)
    (restrictedActionSectionsFromCoord k p (StratumIndex.ofNat i))
    (restrictedActionSectionsFromCoord_vanishingIdeal k p i)

/-- The image of `x_i` remains a unit after the closed coaction. -/
private theorem finiteClosedActionSections_X_isUnit (k : Type u) [Field k] (p i : ℕ) :
    IsUnit
      (finiteClosedActionSections k p i
        (Ideal.Quotient.mk (vanishingIdeal k i) (MvPolynomial.X i))) := sorry

/-- The weighted coaction on the locally closed ring of `𝒳_i`. -/
def finiteLocusActionSections (k : Type u) [Field k] (p i : ℕ) :
    finiteLocusRing k i →+* Γ((restrictedActionDomain k (StratumIndex.ofNat i)).left, ⊤) :=
  IsLocalization.Away.lift
    (Ideal.Quotient.mk (vanishingIdeal k i) (MvPolynomial.X i))
    (finiteClosedActionSections_X_isUnit k p i)

/-- The weighted coaction on the origin ring of `𝒳_∞`. -/
def infinityLocusActionSections (k : Type u) [Field k] (p : ℕ) :
    infinityLocusRing k →+* Γ((restrictedActionDomain k StratumIndex.inf).left, ⊤) :=
  Ideal.Quotient.lift (infinityIdeal k)
    (restrictedActionSectionsFromCoord k p StratumIndex.inf)
    (restrictedActionSectionsFromCoord_infinityIdeal k p)

/-- The underlying scheme morphism of the restricted weighted action. -/
def restrictedActionHomLeft (k : Type u) [Field k] (p : ℕ) (i : StratumIndex) :
    (restrictedActionDomain k i).left ⟶ (locus k i).left :=
  match i with
  | StratumIndex.ofNat n =>
      (Scheme.homToSpecGlobalSectionsEquiv
          (restrictedActionDomain k (StratumIndex.ofNat n)).left
          (CommRingCat.of (finiteLocusRing k n))).symm
        (CommRingCat.ofHom (finiteLocusActionSections k p n))
  | StratumIndex.inf =>
      (Scheme.homToSpecGlobalSectionsEquiv (restrictedActionDomain k StratumIndex.inf).left
          (CommRingCat.of (infinityLocusRing k))).symm
        (CommRingCat.ofHom (infinityLocusActionSections k p))

/-- Compatibility of the restricted action with the structure morphisms to `Spec k`. -/
private theorem restrictedActionHom_w (k : Type u) [Field k] (p : ℕ) (i : StratumIndex) :
    restrictedActionHomLeft k p i ≫ (locus k i).hom = (restrictedActionDomain k i).hom := sorry

/-- The restricted weighted action of `𝔾ₘ[Spec k]` on a stratum locus. -/
def restrictedActionHom (k : Type u) [Field k] (p : ℕ) (i : StratumIndex) :
    restrictedActionDomain k i ⟶ locus k i :=
  Over.homMk (restrictedActionHomLeft k p i) (restrictedActionHom_w k p i)

/-- The underlying scheme map of `restrictedActionHom` is `restrictedActionHomLeft`. -/
theorem restrictedActionHom_left (k : Type u) [Field k] (p : ℕ) (i : StratumIndex) :
    (restrictedActionHom k p i).left = restrictedActionHomLeft k p i := sorry

/-- The identity-action law for the restricted weighted action. -/
private theorem restrictedActionHom_one_smul (k : Type u) [Field k] (p : ℕ) (i : StratumIndex) :
    η[(𝔾ₘ[base k]).X] ⊵ₗ locus k i ≫ restrictedActionHom k p i =
      (λₗ (locus k i)).hom := sorry

/-- The multiplication-action law for the restricted weighted action. -/
private theorem restrictedActionHom_mul_smul (k : Type u) [Field k] (p : ℕ) (i : StratumIndex) :
    μ[(𝔾ₘ[base k]).X] ⊵ₗ locus k i ≫ restrictedActionHom k p i =
      (αₗ (𝔾ₘ[base k]).X (𝔾ₘ[base k]).X (locus k i)).hom ≫
        (𝔾ₘ[base k]).X ⊴ₗ restrictedActionHom k p i ≫ restrictedActionHom k p i := sorry

/-- The module-object structure of the restricted weighted action. -/
@[reducible]
def restrictedSchemeActionModObj (k : Type u) [Field k] (p : ℕ) (i : StratumIndex) :
    ModObj (𝔾ₘ[base k]).X (locus k i) where
  smul := restrictedActionHom k p i
  one_smul := restrictedActionHom_one_smul k p i
  mul_smul := restrictedActionHom_mul_smul k p i

/-- The weighted `𝔾ₘ`-action restricted to a stratum locus. -/
def restrictedSchemeAction (k : Type u) [Field k] (p : ℕ) (i : StratumIndex) :
    GroupScheme.Action (𝔾ₘ[base k]).toGrp where
  X := locus k i
  mod := restrictedSchemeActionModObj k p i

/-- The object underlying `restrictedSchemeAction` is the stratum locus. -/
theorem restrictedSchemeAction_X (k : Type u) [Field k] (p : ℕ) (i : StratumIndex) :
    (restrictedSchemeAction k p i).X = locus k i := sorry

/-- Each stratum locus is invariant under the weighted `𝔾ₘ`-action. -/
theorem isInvariant_locus (k : Type u) [Field k] (p : ℕ) (i : StratumIndex) :
    ∃ φ : restrictedSchemeAction k p i ⟶ schemeAction k p, φ.hom = locusι k i := sorry

/-- The action groupoid of the weighted `𝔾ₘ`-action restricted to a stratum locus. -/
def restrictedGroupoid (k : Type u) [Field k] (p : ℕ) (i : StratumIndex) :
    GroupoidScheme (base k) :=
  GroupoidScheme.ofAction (𝔾ₘ[base k]).toGrp (restrictedSchemeAction k p i)

/-- A stratum locus as an algebraic space over the terminal algebraic space. -/
def locusAsOver (k : Type u) [Field k] (i : StratumIndex) : Over (terminalSpace k) :=
  Over.mk (AlgebraicSpace.ofOverMap (toTerminal k (locus k i)))

/-- Compatibility of the locus immersion with the morphisms to the terminal algebraic space. -/
private theorem locusιAsOver_w (k : Type u) [Field k] (i : StratumIndex) :
    AlgebraicSpace.ofOverMap (locusι k i) ≫ (affineAsOver k).hom =
      (locusAsOver k i).hom := sorry

/-- The equivariant immersion of a stratum locus into infinite affine space, as algebraic spaces. -/
def locusιAsOver (k : Type u) [Field k] (i : StratumIndex) :
    locusAsOver k i ⟶ affineAsOver k :=
  Over.homMk (AlgebraicSpace.ofOverMap (locusι k i)) (locusιAsOver_w k i)

/-- The underlying algebraic-space map of `locusιAsOver` is `ofOverMap` of `locusι`. -/
theorem locusιAsOver_left (k : Type u) [Field k] (i : StratumIndex) :
    (locusιAsOver k i).left = AlgebraicSpace.ofOverMap (locusι k i) := sorry

/-- The first factor of a point of `𝔾ₘ × locus`, as a morphism into `𝔾ₘ[Spec k]`. -/
def restrictedActionPointGroup (k : Type u) [Field k] (i : StratumIndex)
    (T : (Over (base k))ᵒᵖ)
    (x : ((multiplicativeGroup k).X ⊗ locusAsOver k i).left.functorOfPoints.obj T) :
    T.unop ⟶ (𝔾ₘ[base k]).X :=
  (AlgebraicSpace.productSnd (terminalSpace k)
      (AlgebraicSpace.MultiplicativeGroup.ofScheme (base k))).app T
    ((fst (multiplicativeGroup k).X (locusAsOver k i)).left.app T x)

/-- The second factor of a point of `𝔾ₘ × locus`, as a morphism into the stratum locus. -/
def restrictedActionPointSpace (k : Type u) [Field k] (i : StratumIndex)
    (T : (Over (base k))ᵒᵖ)
    (x : ((multiplicativeGroup k).X ⊗ locusAsOver k i).left.functorOfPoints.obj T) :
    T.unop ⟶ locus k i :=
  (snd (multiplicativeGroup k).X (locusAsOver k i)).left.app T x

/-- The algebraic-space morphism `𝔾ₘ × locus → locus` induced by the restricted action. -/
def restrictedActionSmulLeft (k : Type u) [Field k] (p : ℕ) (i : StratumIndex) :
    ((multiplicativeGroup k).X ⊗ locusAsOver k i).left ⟶
      AlgebraicSpace.ofOver (locus k i) where
  app T :=
    ↾fun x ↦
      lift (restrictedActionPointGroup k i T x) (restrictedActionPointSpace k i T x) ≫
        restrictedActionHom k p i
  naturality _ _ _ := sorry

/-- Evaluating `restrictedActionSmulLeft` acts by the restricted scheme-level action. -/
theorem restrictedActionSmulLeft_app (k : Type u) [Field k] (p : ℕ) (i : StratumIndex)
    {T : (Over (base k))ᵒᵖ}
    (x : ((multiplicativeGroup k).X ⊗ locusAsOver k i).left.functorOfPoints.obj T) :
    (restrictedActionSmulLeft k p i).app T x =
      lift (restrictedActionPointGroup k i T x) (restrictedActionPointSpace k i T x) ≫
        restrictedActionHom k p i := sorry

/-- Compatibility of `restrictedActionSmulLeft` with the structure morphisms. -/
private theorem restrictedActionSmul_w (k : Type u) [Field k] (p : ℕ) (i : StratumIndex) :
    restrictedActionSmulLeft k p i ≫ (locusAsOver k i).hom =
      ((multiplicativeGroup k).X ⊗ locusAsOver k i).hom := sorry

/-- The restricted weighted action morphism in the slice over the terminal algebraic space. -/
def restrictedActionSmul (k : Type u) [Field k] (p : ℕ) (i : StratumIndex) :
    (multiplicativeGroup k).X ⊗ locusAsOver k i ⟶ locusAsOver k i :=
  Over.homMk (restrictedActionSmulLeft k p i) (restrictedActionSmul_w k p i)

/-- The identity-action law for the restricted algebraic-space action. -/
private theorem restrictedActionSmul_one_smul (k : Type u) [Field k] (p : ℕ)
    (i : StratumIndex) :
    η[(multiplicativeGroup k).X] ⊵ₗ locusAsOver k i ≫ restrictedActionSmul k p i =
      (λₗ (locusAsOver k i)).hom := sorry

/-- The multiplication-action law for the restricted algebraic-space action. -/
private theorem restrictedActionSmul_mul_smul (k : Type u) [Field k] (p : ℕ)
    (i : StratumIndex) :
    μ[(multiplicativeGroup k).X] ⊵ₗ locusAsOver k i ≫ restrictedActionSmul k p i =
      (αₗ (multiplicativeGroup k).X (multiplicativeGroup k).X (locusAsOver k i)).hom ≫
        (multiplicativeGroup k).X ⊴ₗ restrictedActionSmul k p i ≫
          restrictedActionSmul k p i := sorry

/-- The module-object structure of the restricted algebraic-space action. -/
@[reducible]
def restrictedActionModObj (k : Type u) [Field k] (p : ℕ) (i : StratumIndex) :
    ModObj (multiplicativeGroup k).X (locusAsOver k i) where
  smul := restrictedActionSmul k p i
  one_smul := restrictedActionSmul_one_smul k p i
  mul_smul := restrictedActionSmul_mul_smul k p i

/-- The weighted `𝔾ₘ`-action restricted to a stratum locus, as an algebraic-space action. -/
def restrictedAction (k : Type u) [Field k] (p : ℕ) (hp : Nat.Prime p)
    (i : StratumIndex) :
    GroupAlgebraicSpace.Action (multiplicativeGroup k) where
  X := locusAsOver k i
  mod := restrictedActionModObj k p i

/-- The object underlying `restrictedAction` is the stratum locus as an algebraic space. -/
theorem restrictedAction_X (k : Type u) [Field k] (p : ℕ) (hp : Nat.Prime p)
    (i : StratumIndex) :
    (restrictedAction k p hp i).X = locusAsOver k i := sorry

/-- The action groupoid of the restricted weighted `𝔾ₘ`-action, as a groupoid in algebraic spaces. -/
def restrictedActionGroupoid (k : Type u) [Field k] (p : ℕ) (hp : Nat.Prime p)
    (i : StratumIndex) :
    GroupoidAlgebraicSpace (terminalSpace k) :=
  GroupoidAlgebraicSpace.ofAction (multiplicativeGroup k) (restrictedAction k p hp i)

/-- The quotient stack of the restricted action on a stratum locus. -/
def stratumStack (k : Type u) [Field k] (p : ℕ) (hp : Nat.Prime p)
    (i : StratumIndex) :
    GroupoidsOver (base k) :=
  GroupoidAlgebraicSpace.SmallQuotient.quotientStack (restrictedActionGroupoid k p hp i)

/-- The quotient stack of each restricted action is an algebraic stack. -/
instance instAlgebraicStackStratumStack (k : Type u) [Field k] (p : ℕ)
    (hp : Nat.Prime p) (i : StratumIndex) :
    AlgebraicStack (stratumStack k p hp i) := sorry

/-- The quotient of each weighted invariant locus is a reduced algebraic stack. -/
instance instIsReducedStratumStack (k : Type u) [Field k] (p : ℕ)
    (hp : Nat.Prime p) (i : StratumIndex) :
    AlgebraicStack.IsReduced (stratumStack k p hp i) := sorry

/-- The locus inclusion commutes with the source maps of the action groupoids. -/
private theorem stratumGroupoidHom_map_s (k : Type u) [Field k] (p : ℕ)
    (hp : Nat.Prime p) (i : StratumIndex) :
    (restrictedActionGroupoid k p hp i).s ≫ locusιAsOver k i =
      whiskerLeft (multiplicativeGroup k).X (locusιAsOver k i) ≫ (groupoid k p hp).s := sorry

/-- The locus inclusion commutes with the target maps of the action groupoids. -/
private theorem stratumGroupoidHom_map_t (k : Type u) [Field k] (p : ℕ)
    (hp : Nat.Prime p) (i : StratumIndex) :
    (restrictedActionGroupoid k p hp i).t ≫ locusιAsOver k i =
      whiskerLeft (multiplicativeGroup k).X (locusιAsOver k i) ≫ (groupoid k p hp).t := sorry

/-- The locus inclusion preserves composition in the action groupoids. -/
private theorem stratumGroupoidHom_map_c (k : Type u) [Field k] (p : ℕ)
    (hp : Nat.Prime p) (i : StratumIndex) :
    (restrictedActionGroupoid k p hp i).c ≫
        whiskerLeft (multiplicativeGroup k).X (locusιAsOver k i) =
      GroupoidAlgebraicSpace.composableMap (locusιAsOver k i)
        (whiskerLeft (multiplicativeGroup k).X (locusιAsOver k i))
        (stratumGroupoidHom_map_s k p hp i) (stratumGroupoidHom_map_t k p hp i) ≫
          (groupoid k p hp).c := sorry

/-- The groupoid morphism induced by the equivariant immersion of a stratum locus. -/
def stratumGroupoidHom (k : Type u) [Field k] (p : ℕ) (hp : Nat.Prime p)
    (i : StratumIndex) :
    GroupoidAlgebraicSpace.Hom (restrictedActionGroupoid k p hp i) (groupoid k p hp) where
  obj := locusιAsOver k i
  arrow := whiskerLeft (multiplicativeGroup k).X (locusιAsOver k i)
  map_s := stratumGroupoidHom_map_s k p hp i
  map_t := stratumGroupoidHom_map_t k p hp i
  map_c := stratumGroupoidHom_map_c k p hp i

/-- The quotient morphism induced by the equivariant immersion of a stratum locus. -/
def stratumι (k : Type u) [Field k] (p : ℕ) (hp : Nat.Prime p)
    (i : StratumIndex) : stratumStack k p hp i ⟶ stack k p hp :=
  GroupoidAlgebraicSpace.Hom.quotientStackHom (stratumGroupoidHom k p hp i)

/-- The restricted-quotient inclusion of each stratum is an immersion. -/
instance instImmersionStratumι (k : Type u) [Field k] (p : ℕ) (hp : Nat.Prime p)
    (i : StratumIndex) : Immersion (stratumι k p hp i) := sorry

/-- Pullback of `μ_{p^i}` along the finite stratum locus. -/
def finiteLocusRootsOfUnity (k : Type u) [Field k] (p i : ℕ) (hp : Nat.Prime p) :
    GroupScheme (finiteLocus k i).left :=
  GroupScheme.baseChange
    (@RootsOfUnity.baseChange (p ^ i) ⟨pow_ne_zero i hp.ne_zero⟩ (base k)).toGrp
    (finiteLocus k i).hom

/-- Pullback of `𝔾ₘ[Spec k]` along the origin locus. -/
def infinityLocusMultiplicativeGroup (k : Type u) [Field k] :
    GroupScheme (infinityLocus k).left :=
  GroupScheme.baseChange (𝔾ₘ[base k]).toGrp (infinityLocus k).hom

/-- The stabilizer of the restricted finite-stratum action, as a group scheme over that locus. -/
def finiteLocusStabilizer (k : Type u) [Field k] (p i : ℕ) :
    GroupScheme (finiteLocus k i).left :=
  (Over.iteratedSliceEquiv (finiteLocus k i)).functor.mapGrp.obj
    (GroupoidScheme.stabilizer (restrictedGroupoid k p (StratumIndex.ofNat i)))

/-- The stabilizer of the restricted origin action, as a group scheme over the origin locus. -/
def infinityLocusStabilizer (k : Type u) [Field k] (p : ℕ) :
    GroupScheme (infinityLocus k).left :=
  (Over.iteratedSliceEquiv (infinityLocus k)).functor.mapGrp.obj
    (GroupoidScheme.stabilizer (restrictedGroupoid k p StratumIndex.inf))

/-- On the finite locus, the restricted stabilizer is the pullback of `μ_{p^i}` as group schemes. -/
theorem restrictedStabilizer_iso_rootsOfUnity (k : Type u) [Field k] (p i : ℕ)
    (hp : Nat.Prime p) :
    Nonempty (finiteLocusStabilizer k p i ≅ finiteLocusRootsOfUnity k p i hp) := sorry

/-- On the origin locus, the restricted stabilizer is the pullback of `𝔾ₘ` as group schemes. -/
theorem restrictedStabilizer_iso_multiplicativeGroup (k : Type u) [Field k] (p : ℕ)
    (hp : Nat.Prime p) :
    Nonempty (infinityLocusStabilizer k p ≅ infinityLocusMultiplicativeGroup k) := sorry

/-- Each finite stratum is a gerbe over a scheme with group `μ_{p^i}`. -/
theorem isGerbeOver_rootsOfUnity (k : Type u) [Field k] (p : ℕ) (hp : Nat.Prime p)
    (i : ℕ) :
    ∃ (Y : Over (base k))
      (f : stratumStack k p hp (StratumIndex.ofNat i) ⟶ GroupoidsOver.slice Y),
      IsGerbeMorphism (Scheme.fppfTopology.over (base k)) f ∧
        Nonempty (finiteLocusStabilizer k p i ≅ finiteLocusRootsOfUnity k p i hp) := sorry

/-- The infinite stratum is a gerbe over a scheme with group `𝔾ₘ`. -/
theorem isGerbeOver_multiplicativeGroup (k : Type u) [Field k] (p : ℕ)
    (hp : Nat.Prime p) :
    ∃ (Y : Over (base k))
      (f : stratumStack k p hp StratumIndex.inf ⟶ GroupoidsOver.slice Y),
      IsGerbeMorphism (Scheme.fppfTopology.over (base k)) f ∧
        Nonempty (infinityLocusStabilizer k p ≅ infinityLocusMultiplicativeGroup k) := sorry

/-- The images of the strata partition the points of `[U / 𝔾ₘ]`. -/
theorem isStratification (k : Type u) [Field k] (p : ℕ) (hp : Nat.Prime p) :
    (∀ x : Points (stack k p hp),
        ∃ i : StratumIndex, x ∈ Set.range (Points.map (stratumι k p hp i))) ∧
      Pairwise fun i j : StratumIndex ↦
        Disjoint (Set.range (Points.map (stratumι k p hp i)))
          (Set.range (Points.map (stratumι k p hp j))) := sorry

/-- A reduced locally closed gerbe whose image is a nonempty union of the weighted
strata contains exactly one of these strata. -/
theorem isCoarsest (k : Type u) [Field k] (p : ℕ) (hp : Nat.Prime p)
    (Z : GroupoidsOver (base k)) [AlgebraicStack Z]
    (f : Z ⟶ stack k p hp) [Immersion f] (I : Set StratumIndex)
    (h_reduced : AlgebraicStack.IsReduced Z)
    (h_nonempty : I.Nonempty)
    (h_gerbe : ∃ (S : Over (base k)) (g : Z ⟶ GroupoidsOver.slice S),
      IsGerbeMorphism (Scheme.fppfTopology.over (base k)) g)
    (h_union : Set.range (Points.map f) =
      ⋃ i ∈ I, Set.range (Points.map (stratumι k p hp i))) :
    ∃ i : StratumIndex, I = {i} := sorry

end AlgebraicGeometry.AlgebraicStack.WeightedInfiniteAffine
