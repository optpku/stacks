/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.TensorProduct.Basic
public import ReasLib.AlgebraicGeometry.GroupScheme.Action
public import ReasLib.AlgebraicGeometry.MultiplicativeGroup
public import ReasLib.AlgebraicGeometry.Scheme.OverSpec
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Action
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.MultiplicativeGroup
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Product
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Action
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Small
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic

/-!
# Weighted 𝔾ₘ-action on infinite affine space

This module constructs the affine space `U = Spec(k[x_i | i : ℕ])` over a field `k`, the
weighted coaction `x_i ↦ T^(p^i) ⊗ x_i`, the induced action of `𝔾ₘ` over `Spec k`, and the
quotient stack `[U / 𝔾ₘ]`.
-/

@[expose] public section

set_option backward.privateInPublic true

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Limits
open CartesianMonoidalCategory MonoidalCategory
open scoped AlgebraicGeometry CategoryTheory.MonObj MonoidalLeftAction TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.WeightedInfiniteAffine

/-- The coordinate ring `k[x_i | i : ℕ]` of infinite affine space. -/
abbrev coordRing (k : Type u) [Field k] : Type u :=
  MvPolynomial ℕ k

/-- The base scheme `S = Spec k`. -/
abbrev base (k : Type u) [Field k] : Scheme.{u} :=
  Spec (CommRingCat.of k)

/-- Infinite affine space `U = Spec(k[x_i | i : ℕ])` as a scheme over `Spec k`. -/
def affineSpace (k : Type u) [Field k] : Over (base k) :=
  OverSpec.affine (CommRingCat.ofHom (algebraMap k (coordRing k)))

/-- The underlying scheme of `affineSpace k` is `Spec` of the coordinate ring. -/
theorem affineSpace_left (k : Type u) [Field k] :
    (affineSpace k).left = Spec (CommRingCat.of (coordRing k)) := sorry

/-- The structure morphism of `affineSpace k` is induced by `algebraMap k (coordRing k)`. -/
theorem affineSpace_hom (k : Type u) [Field k] :
    (affineSpace k).hom = Spec.map (CommRingCat.ofHom (algebraMap k (coordRing k))) := sorry

/-- The weighted Laurent coaction `x_i ↦ T^(p^i) ⊗ x_i` on the coordinate ring. -/
def coaction (k : Type u) [Field k] (p : ℕ) :
    coordRing k →ₐ[k] LaurentPolynomial k ⊗[k] coordRing k :=
  MvPolynomial.aeval fun i ↦ LaurentPolynomial.T (p ^ i : ℤ) ⊗ₜ[k] MvPolynomial.X i

/-- The coaction sends the coordinate `x_i` to `T^(p^i) ⊗ x_i`. -/
theorem coaction_X (k : Type u) [Field k] (p i : ℕ) :
    coaction k p (MvPolynomial.X i) =
      LaurentPolynomial.T (p ^ i : ℤ) ⊗ₜ[k] (MvPolynomial.X i : coordRing k) := sorry

/-- The domain `𝔾ₘ[Spec k] ×_Spec k U` of the scheme-level weighted action. -/
def actionDomain (k : Type u) [Field k] : Over (base k) :=
  (𝔾ₘ[base k]).X ⊗ affineSpace k

/-- The unit pulled back from `𝔾ₘ[Spec k]` along the first projection of `actionDomain`. -/
def actionDomainUnit (k : Type u) [Field k] : Γ((actionDomain k).left, ⊤)ˣ :=
  MultiplicativeGroup.baseChangeHomEquiv (base k) (actionDomain k)
    (fst (𝔾ₘ[base k]).X (affineSpace k))

/-- The coordinate ring map pulled back along the second projection of `actionDomain`. -/
def actionDomainCoord (k : Type u) [Field k] :
    coordRing k →+* Γ((actionDomain k).left, ⊤) :=
  (Scheme.homToSpecGlobalSectionsEquiv (actionDomain k).left
      (CommRingCat.of (coordRing k))
      (snd (𝔾ₘ[base k]).X (affineSpace k)).left).hom

/-- The ring map `k → Γ(actionDomain, ⊤)` induced by the structure morphism. -/
def actionDomainBase (k : Type u) [Field k] :
    k →+* Γ((actionDomain k).left, ⊤) :=
  (Scheme.homToSpecGlobalSectionsEquiv (actionDomain k).left (CommRingCat.of k)
      (actionDomain k).hom).hom

/-- The weighted action on global sections, sending `x_i` to `t^(p^i) x_i`. -/
def actionSections (k : Type u) [Field k] (p : ℕ) :
    coordRing k →+* Γ((actionDomain k).left, ⊤) :=
  MvPolynomial.eval₂Hom (actionDomainBase k) fun i ↦
    ((actionDomainUnit k ^ p ^ i : Γ((actionDomain k).left, ⊤)ˣ) : Γ((actionDomain k).left, ⊤)) *
      actionDomainCoord k (MvPolynomial.X i)

/-- The underlying scheme morphism of the weighted `𝔾ₘ`-action. -/
def actionHomLeft (k : Type u) [Field k] (p : ℕ) :
    (actionDomain k).left ⟶ (affineSpace k).left :=
  (Scheme.homToSpecGlobalSectionsEquiv (actionDomain k).left
      (CommRingCat.of (coordRing k))).symm
    (CommRingCat.ofHom (actionSections k p))

/-- Compatibility of `actionHomLeft` with the structure morphisms to `Spec k`. -/
private theorem actionHom_w (k : Type u) [Field k] (p : ℕ) :
    actionHomLeft k p ≫ (affineSpace k).hom = (actionDomain k).hom := sorry

/-- The weighted action of `𝔾ₘ[Spec k]` on infinite affine space. -/
def actionHom (k : Type u) [Field k] (p : ℕ) : actionDomain k ⟶ affineSpace k :=
  Over.homMk (actionHomLeft k p) (actionHom_w k p)

/-- The underlying scheme map of `actionHom` is `actionHomLeft`. -/
theorem actionHom_left (k : Type u) [Field k] (p : ℕ) :
    (actionHom k p).left = actionHomLeft k p := sorry

/-- The identity-action law for the weighted `𝔾ₘ`-action. -/
private theorem actionHom_one_smul (k : Type u) [Field k] (p : ℕ) :
    η[(𝔾ₘ[base k]).X] ⊵ₗ affineSpace k ≫ actionHom k p =
      (λₗ (affineSpace k)).hom := sorry

/-- The multiplication-action law for the weighted `𝔾ₘ`-action. -/
private theorem actionHom_mul_smul (k : Type u) [Field k] (p : ℕ) :
    μ[(𝔾ₘ[base k]).X] ⊵ₗ affineSpace k ≫ actionHom k p =
      (αₗ (𝔾ₘ[base k]).X (𝔾ₘ[base k]).X (affineSpace k)).hom ≫
        (𝔾ₘ[base k]).X ⊴ₗ actionHom k p ≫ actionHom k p := sorry

/-- The module-object structure of the weighted scheme-level action. -/
@[reducible]
def schemeActionModObj (k : Type u) [Field k] (p : ℕ) :
    ModObj (𝔾ₘ[base k]).X (affineSpace k) where
  smul := actionHom k p
  one_smul := actionHom_one_smul k p
  mul_smul := actionHom_mul_smul k p

/-- The weighted action of `𝔾ₘ[Spec k]` on infinite affine space, as a group-scheme action. -/
def schemeAction (k : Type u) [Field k] (p : ℕ) : GroupScheme.Action (𝔾ₘ[base k]).toGrp where
  X := affineSpace k
  mod := schemeActionModObj k p

/-- The object underlying `schemeAction` is infinite affine space. -/
theorem schemeAction_X (k : Type u) [Field k] (p : ℕ) :
    (schemeAction k p).X = affineSpace k := sorry

/-- The stored scheme-level action morphism is `actionHom`. -/
theorem schemeAction_smul (k : Type u) [Field k] (p : ℕ) :
    (schemeAction k p).mod.smul = actionHom k p := sorry

/-- The terminal algebraic space `Spec k` over itself. -/
def terminalSpace (k : Type u) [Field k] : AlgebraicSpace (base k) :=
  AlgebraicSpace.ofOver (Over.mk (𝟙 (base k)))

/-- The unique morphism from a scheme over `Spec k` to the identity object. -/
def toTerminal (k : Type u) [Field k] (T : Over (base k)) :
    T ⟶ Over.mk (𝟙 (base k)) :=
  Over.homMk T.hom (Category.comp_id T.hom)

/-- Infinite affine space as an algebraic space over the terminal algebraic space. -/
def affineAsOver (k : Type u) [Field k] : Over (terminalSpace k) :=
  Over.mk (AlgebraicSpace.ofOverMap (toTerminal k (affineSpace k)))

/-- The multiplicative group algebraic space `𝔾ₘ` over `Spec k`. -/
def multiplicativeGroup (k : Type u) [Field k] : GroupAlgebraicSpace (terminalSpace k) :=
  AlgebraicSpace.MultiplicativeGroup.groupSpace (terminalSpace k)

/-- The first factor of a point of `𝔾ₘ × U`, as a morphism into `𝔾ₘ[Spec k]`. -/
def actionPointGroup (k : Type u) [Field k] (T : (Over (base k))ᵒᵖ)
    (x : ((multiplicativeGroup k).X ⊗ affineAsOver k).left.functorOfPoints.obj T) :
    T.unop ⟶ (𝔾ₘ[base k]).X :=
  (AlgebraicSpace.productSnd (terminalSpace k)
      (AlgebraicSpace.MultiplicativeGroup.ofScheme (base k))).app T
    ((fst (multiplicativeGroup k).X (affineAsOver k)).left.app T x)

/-- The second factor of a point of `𝔾ₘ × U`, as a morphism into infinite affine space. -/
def actionPointSpace (k : Type u) [Field k] (T : (Over (base k))ᵒᵖ)
    (x : ((multiplicativeGroup k).X ⊗ affineAsOver k).left.functorOfPoints.obj T) :
    T.unop ⟶ affineSpace k :=
  (snd (multiplicativeGroup k).X (affineAsOver k)).left.app T x

/-- The algebraic-space morphism `𝔾ₘ × U → U` induced by the weighted scheme-level action. -/
def actionSmulLeft (k : Type u) [Field k] (p : ℕ) :
    ((multiplicativeGroup k).X ⊗ affineAsOver k).left ⟶
      AlgebraicSpace.ofOver (affineSpace k) where
  app T :=
    ↾fun x ↦ lift (actionPointGroup k T x) (actionPointSpace k T x) ≫ actionHom k p
  naturality _ _ _ := sorry

/-- Evaluating `actionSmulLeft` acts by the scheme-level weighted action on paired points. -/
theorem actionSmulLeft_app (k : Type u) [Field k] (p : ℕ)
    {T : (Over (base k))ᵒᵖ}
    (x : ((multiplicativeGroup k).X ⊗ affineAsOver k).left.functorOfPoints.obj T) :
    (actionSmulLeft k p).app T x =
      lift (actionPointGroup k T x) (actionPointSpace k T x) ≫ actionHom k p := sorry

/-- Compatibility of `actionSmulLeft` with the structure morphisms over the terminal algebraic
space. -/
private theorem actionSmul_w (k : Type u) [Field k] (p : ℕ) :
    actionSmulLeft k p ≫ (affineAsOver k).hom =
      ((multiplicativeGroup k).X ⊗ affineAsOver k).hom := sorry

/-- The weighted action morphism in the slice over the terminal algebraic space. -/
def actionSmul (k : Type u) [Field k] (p : ℕ) :
    (multiplicativeGroup k).X ⊗ affineAsOver k ⟶ affineAsOver k :=
  Over.homMk (actionSmulLeft k p) (actionSmul_w k p)

/-- The identity-action law for the algebraic-space weighted action. -/
private theorem actionSmul_one_smul (k : Type u) [Field k] (p : ℕ) :
    η[(multiplicativeGroup k).X] ⊵ₗ affineAsOver k ≫ actionSmul k p =
      (λₗ (affineAsOver k)).hom := sorry

/-- The multiplication-action law for the algebraic-space weighted action. -/
private theorem actionSmul_mul_smul (k : Type u) [Field k] (p : ℕ) :
    μ[(multiplicativeGroup k).X] ⊵ₗ affineAsOver k ≫ actionSmul k p =
      (αₗ (multiplicativeGroup k).X (multiplicativeGroup k).X (affineAsOver k)).hom ≫
        (multiplicativeGroup k).X ⊴ₗ actionSmul k p ≫ actionSmul k p := sorry

/-- The module-object structure of the weighted algebraic-space action. -/
@[reducible]
def actionModObj (k : Type u) [Field k] (p : ℕ) :
    ModObj (multiplicativeGroup k).X (affineAsOver k) where
  smul := actionSmul k p
  one_smul := actionSmul_one_smul k p
  mul_smul := actionSmul_mul_smul k p

/-- The weighted action of `𝔾ₘ` on infinite affine space, as an action of a group algebraic
space. -/
def action (k : Type u) [Field k] (p : ℕ) (hp : Nat.Prime p) :
    GroupAlgebraicSpace.Action (multiplicativeGroup k) where
  X := affineAsOver k
  mod := actionModObj k p

/-- The stored action morphism of `action` is `actionSmul`. -/
theorem action_smul (k : Type u) [Field k] (p : ℕ) (hp : Nat.Prime p) :
    (action k p hp).mod.smul = actionSmul k p := sorry

/-- The action groupoid of the weighted `𝔾ₘ`-action on infinite affine space. -/
def groupoid (k : Type u) [Field k] (p : ℕ) (hp : Nat.Prime p) :
    GroupoidAlgebraicSpace (terminalSpace k) :=
  GroupoidAlgebraicSpace.ofAction (multiplicativeGroup k) (action k p hp)

/-- The quotient stack `𝒳 = [U / 𝔾ₘ]` of the weighted action. -/
def stack (k : Type u) [Field k] (p : ℕ) (hp : Nat.Prime p) :
    GroupoidsOver (base k) :=
  GroupoidAlgebraicSpace.SmallQuotient.quotientStack (groupoid k p hp)

/-- The quotient stack `[U / 𝔾ₘ]` of the weighted action is an algebraic stack. -/
instance instAlgebraicStack (k : Type u) [Field k] (p : ℕ) (hp : Nat.Prime p) :
    AlgebraicStack (stack k p hp) := sorry

/-- The atlas `U ⟶ [U / 𝔾ₘ]` of the weighted quotient stack. -/
def atlas (k : Type u) [Field k] (p : ℕ) (hp : Nat.Prime p) :
    (AlgebraicSpace.ofOver (affineSpace k)).toGroupoids ⟶ stack k p hp :=
  GroupoidAlgebraicSpace.SmallQuotient.atlas (groupoid k p hp)

end AlgebraicGeometry.AlgebraicStack.WeightedInfiniteAffine
