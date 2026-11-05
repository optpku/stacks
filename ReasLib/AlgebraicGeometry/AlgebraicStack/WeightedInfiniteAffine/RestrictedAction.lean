/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.WeightedInfiniteAffine.Locus
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Action

/-!
# Restricted weighted actions on the stratum loci

The coordinate coaction descends to each locus, defining restricted actions and
action groupoids in schemes and algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Limits
open CartesianMonoidalCategory MonoidalCategory
open scoped AlgebraicGeometry CategoryTheory.MonObj MonoidalLeftAction

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.WeightedInfiniteAffine

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
theorem restrictedActionSectionsFromCoord_vanishingIdeal (k : Type u) [Field k] (p i : ℕ)
    (f : coordRing k) (hf : f ∈ vanishingIdeal k i) :
    restrictedActionSectionsFromCoord k p (StratumIndex.ofNat i) f = 0 := sorry
/-- The pulled-back coaction vanishes on every coordinate at the origin. -/
theorem restrictedActionSectionsFromCoord_infinityIdeal (k : Type u) [Field k] (p : ℕ)
    (f : coordRing k) (hf : f ∈ infinityIdeal k) :
    restrictedActionSectionsFromCoord k p StratumIndex.inf f = 0 := sorry
/-- The weighted coaction on the closed subscheme ring of `𝒳_i`. -/
def finiteClosedActionSections (k : Type u) [Field k] (p i : ℕ) :
    finiteClosedRing k i →+* Γ((restrictedActionDomain k (StratumIndex.ofNat i)).left, ⊤) :=
  Ideal.Quotient.lift (vanishingIdeal k i)
    (restrictedActionSectionsFromCoord k p (StratumIndex.ofNat i))
    (restrictedActionSectionsFromCoord_vanishingIdeal k p i)
/-- The image of `x_i` remains a unit after the closed coaction. -/
theorem finiteClosedActionSections_X_isUnit (k : Type u) [Field k] (p i : ℕ) :
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
theorem restrictedActionHom_w (k : Type u) [Field k] (p : ℕ) (i : StratumIndex) :
    restrictedActionHomLeft k p i ≫ (locus k i).hom = (restrictedActionDomain k i).hom := sorry
/-- The restricted weighted action of `𝔾ₘ[Spec k]` on a stratum locus. -/
def restrictedActionHom (k : Type u) [Field k] (p : ℕ) (i : StratumIndex) :
    restrictedActionDomain k i ⟶ locus k i :=
  Over.homMk (restrictedActionHomLeft k p i) (restrictedActionHom_w k p i)
/-- The underlying scheme map of `restrictedActionHom` is `restrictedActionHomLeft`. -/
theorem restrictedActionHom_left (k : Type u) [Field k] (p : ℕ) (i : StratumIndex) :
    (restrictedActionHom k p i).left = restrictedActionHomLeft k p i := sorry
/-- The identity-action law for the restricted weighted action. -/
theorem restrictedActionHom_one_smul (k : Type u) [Field k] (p : ℕ) (i : StratumIndex) :
    η[(𝔾ₘ[base k]).X] ⊵ₗ locus k i ≫ restrictedActionHom k p i =
      (λₗ (locus k i)).hom := sorry
/-- The multiplication-action law for the restricted weighted action. -/
theorem restrictedActionHom_mul_smul (k : Type u) [Field k] (p : ℕ) (i : StratumIndex) :
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
theorem locusιAsOver_w (k : Type u) [Field k] (i : StratumIndex) :
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
theorem restrictedActionSmul_w (k : Type u) [Field k] (p : ℕ) (i : StratumIndex) :
    restrictedActionSmulLeft k p i ≫ (locusAsOver k i).hom =
      ((multiplicativeGroup k).X ⊗ locusAsOver k i).hom := sorry
/-- The restricted weighted action morphism in the slice over the terminal algebraic space. -/
def restrictedActionSmul (k : Type u) [Field k] (p : ℕ) (i : StratumIndex) :
    (multiplicativeGroup k).X ⊗ locusAsOver k i ⟶ locusAsOver k i :=
  Over.homMk (restrictedActionSmulLeft k p i) (restrictedActionSmul_w k p i)

/-- The identity-action law for the restricted algebraic-space action. -/
theorem restrictedActionSmul_one_smul (k : Type u) [Field k] (p : ℕ)
    (i : StratumIndex) :
    η[(multiplicativeGroup k).X] ⊵ₗ locusAsOver k i ≫ restrictedActionSmul k p i =
      (λₗ (locusAsOver k i)).hom := sorry

/-- The multiplication-action law for the restricted algebraic-space action. -/
theorem restrictedActionSmul_mul_smul (k : Type u) [Field k] (p : ℕ)
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

end AlgebraicGeometry.AlgebraicStack.WeightedInfiniteAffine
