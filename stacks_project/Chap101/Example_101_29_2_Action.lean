module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.TensorProduct.Basic
public import ReasLib.AlgebraicGeometry.GroupScheme.Action
public import ReasLib.AlgebraicGeometry.MultiplicativeGroup
public import ReasLib.AlgebraicGeometry.Scheme.OverSpec
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap78.Definition_78_8_1_Action
public import stacks_project.Chap78.Example_78_7_1_Multiplicative_group_algebraic_space_MultiplicativeGroup
public import stacks_project.Chap78.Lemma_78_15_1_Action
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap94.Definition_94_16_5_Quotient

/-!
# Weighted 𝔾ₘ-action on infinite affine space

This module constructs the affine space `U = Spec(k[x_i | i : ℕ])` over a field `k`, the
weighted coaction `x_i ↦ T^(p^i) ⊗ x_i`, the induced action of `𝔾ₘ` over `Spec k`, and the
quotient stack `[U / 𝔾ₘ]`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Limits
open CartesianMonoidalCategory MonoidalCategory
open scoped AlgebraicGeometry CategoryTheory.MonObj MonoidalLeftAction TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.WeightedInfiniteAffine

/-- The coordinate ring `k[x_i | i : ℕ]` of infinite affine space. -/
abbrev coordRing (k : Type u) [Field k] : Type u :=
  MvPolynomial ℕ k

/-- The coordinate ring is the polynomial ring on countably many variables. -/
theorem coordRing_eq (k : Type u) [Field k] : coordRing k = MvPolynomial ℕ k :=
  sorry

/-- The `i`-th coordinate function on infinite affine space. -/
def coordRing.X (k : Type u) [Field k] (i : ℕ) : coordRing k :=
  MvPolynomial.X i

/-- `coordRing.X k i` is the variable `MvPolynomial.X i`. -/
theorem coordRing.X_eq (k : Type u) [Field k] (i : ℕ) :
    coordRing.X k i = MvPolynomial.X i :=
  sorry

/-- The base scheme `S = Spec k`. -/
abbrev base (k : Type u) [Field k] : Scheme.{u} :=
  Spec (CommRingCat.of k)

/-- The base scheme is the spectrum of `k`. -/
theorem base_eq (k : Type u) [Field k] : base k = Spec (CommRingCat.of k) :=
  sorry

/-- Infinite affine space `U = Spec(k[x_i | i : ℕ])` as a scheme over `Spec k`. -/
def affineSpace (k : Type u) [Field k] : Over (base k) :=
  OverSpec.affine (CommRingCat.ofHom (algebraMap k (coordRing k)))

/-- The underlying scheme of `affineSpace k` is `Spec` of the coordinate ring. -/
theorem affineSpace_left (k : Type u) [Field k] :
    (affineSpace k).left = Spec (CommRingCat.of (coordRing k)) :=
  sorry

/-- The structure morphism of `affineSpace k` is induced by `algebraMap k (coordRing k)`. -/
theorem affineSpace_hom (k : Type u) [Field k] :
    (affineSpace k).hom = Spec.map (CommRingCat.ofHom (algebraMap k (coordRing k))) :=
  sorry

/-- The weight `p^i` of the coordinate `x_i`. -/
def weight (p i : ℕ) : ℕ :=
  p ^ i

/-- The weight of `x_i` is `p ^ i`. -/
theorem weight_eq (p i : ℕ) : weight p i = p ^ i :=
  sorry

/-- The weight of `x_0` is `1`. -/
theorem weight_zero (p : ℕ) : weight p 0 = 1 :=
  sorry

/-- The weight of `x_{i+1}` is `p` times the weight of `x_i`. -/
theorem weight_succ (p i : ℕ) : weight p (i + 1) = p * weight p i :=
  sorry

/-- A prime has nonzero weights `p^i`. -/
theorem weight_ne_zero {p : ℕ} (hp : Nat.Prime p) (i : ℕ) : weight p i ≠ 0 :=
  sorry

/-- The weighted Laurent coaction `x_i ↦ T^(p^i) ⊗ x_i` on the coordinate ring. -/
def coaction (k : Type u) [Field k] (p : ℕ) :
    coordRing k →ₐ[k] LaurentPolynomial k ⊗[k] coordRing k :=
  MvPolynomial.aeval fun i ↦ LaurentPolynomial.T (p ^ i : ℤ) ⊗ₜ[k] MvPolynomial.X i

/-- The coaction sends the coordinate `x_i` to `T^(p^i) ⊗ x_i`. -/
theorem coaction_X (k : Type u) [Field k] (p i : ℕ) :
    coaction k p (MvPolynomial.X i) =
      LaurentPolynomial.T (p ^ i : ℤ) ⊗ₜ[k] (MvPolynomial.X i : coordRing k) :=
  sorry

/-- The domain `𝔾ₘ[Spec k] ×_Spec k U` of the scheme-level weighted action. -/
def actionDomain (k : Type u) [Field k] : Over (base k) :=
  (𝔾ₘ[base k]).X ⊗ affineSpace k

/-- `actionDomain k` is the Cartesian product of `𝔾ₘ[Spec k]` with infinite affine space. -/
theorem actionDomain_eq (k : Type u) [Field k] :
    actionDomain k = (𝔾ₘ[base k]).X ⊗ affineSpace k :=
  sorry

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

/-- `actionHomLeft` is classified by `actionSections`. -/
theorem actionHomLeft_eq (k : Type u) [Field k] (p : ℕ) :
    actionHomLeft k p =
      (Scheme.homToSpecGlobalSectionsEquiv (actionDomain k).left
          (CommRingCat.of (coordRing k))).symm
        (CommRingCat.ofHom (actionSections k p)) :=
  sorry

/-- Compatibility of `actionHomLeft` with the structure morphisms to `Spec k`. -/
theorem actionHom_w (k : Type u) [Field k] (p : ℕ) :
    actionHomLeft k p ≫ (affineSpace k).hom = (actionDomain k).hom :=
  sorry

/-- The weighted action of `𝔾ₘ[Spec k]` on infinite affine space. -/
def actionHom (k : Type u) [Field k] (p : ℕ) : actionDomain k ⟶ affineSpace k :=
  Over.homMk (actionHomLeft k p) (actionHom_w k p)

/-- The underlying scheme map of `actionHom` is `actionHomLeft`. -/
theorem actionHom_left (k : Type u) [Field k] (p : ℕ) :
    (actionHom k p).left = actionHomLeft k p :=
  sorry

/-- The identity-action law for the weighted `𝔾ₘ`-action. -/
theorem actionHom_one_smul (k : Type u) [Field k] (p : ℕ) :
    η[(𝔾ₘ[base k]).X] ⊵ₗ affineSpace k ≫ actionHom k p =
      (λₗ (affineSpace k)).hom :=
  sorry

/-- The multiplication-action law for the weighted `𝔾ₘ`-action. -/
theorem actionHom_mul_smul (k : Type u) [Field k] (p : ℕ) :
    μ[(𝔾ₘ[base k]).X] ⊵ₗ affineSpace k ≫ actionHom k p =
      (αₗ (𝔾ₘ[base k]).X (𝔾ₘ[base k]).X (affineSpace k)).hom ≫
        (𝔾ₘ[base k]).X ⊴ₗ actionHom k p ≫ actionHom k p :=
  sorry

/-- The module-object structure of the weighted scheme-level action. -/
@[reducible]
def schemeActionModObj (k : Type u) [Field k] (p : ℕ) :
    ModObj (𝔾ₘ[base k]).X (affineSpace k) where
  smul := actionHom k p
  one_smul := actionHom_one_smul k p
  mul_smul := actionHom_mul_smul k p

/-- The stored scheme-level action morphism is `actionHom`. -/
theorem schemeActionModObj_smul (k : Type u) [Field k] (p : ℕ) :
    (schemeActionModObj k p).smul = actionHom k p :=
  sorry

/-- The weighted action of `𝔾ₘ[Spec k]` on infinite affine space, as a group-scheme action. -/
def schemeAction (k : Type u) [Field k] (p : ℕ) : GroupScheme.Action (𝔾ₘ[base k]).toGrp where
  X := affineSpace k
  mod := schemeActionModObj k p

/-- The object underlying `schemeAction` is infinite affine space. -/
theorem schemeAction_X (k : Type u) [Field k] (p : ℕ) :
    (schemeAction k p).X = affineSpace k :=
  sorry

/-- The stored scheme-level action morphism is `actionHom`. -/
theorem schemeAction_smul (k : Type u) [Field k] (p : ℕ) :
    (schemeAction k p).mod.smul = actionHom k p :=
  sorry

/-- The terminal algebraic space `Spec k` over itself. -/
def terminalSpace (k : Type u) [Field k] : AlgebraicSpace (base k) :=
  AlgebraicSpace.ofOver (Over.mk (𝟙 (base k)))

/-- `terminalSpace k` is `ofOver` of the identity over `Spec k`. -/
theorem terminalSpace_eq (k : Type u) [Field k] :
    terminalSpace k = AlgebraicSpace.ofOver (Over.mk (𝟙 (base k))) :=
  sorry

/-- The unique morphism from a scheme over `Spec k` to the identity object. -/
def toTerminal (k : Type u) [Field k] (T : Over (base k)) :
    T ⟶ Over.mk (𝟙 (base k)) :=
  Over.homMk T.hom (Category.comp_id T.hom)

/-- The underlying scheme map of `toTerminal T` is the structure morphism of `T`. -/
theorem toTerminal_left (k : Type u) [Field k] (T : Over (base k)) :
    (toTerminal k T).left = T.hom :=
  sorry

/-- Infinite affine space as an algebraic space over the terminal algebraic space. -/
def affineAsOver (k : Type u) [Field k] : Over (terminalSpace k) :=
  Over.mk (AlgebraicSpace.ofOverMap (toTerminal k (affineSpace k)))

/-- The underlying algebraic space of `affineAsOver k` is `ofOver` of infinite affine space. -/
theorem affineAsOver_left (k : Type u) [Field k] :
    (affineAsOver k).left = AlgebraicSpace.ofOver (affineSpace k) :=
  sorry

/-- The multiplicative group algebraic space `𝔾ₘ` over `Spec k`. -/
def multiplicativeGroup (k : Type u) [Field k] : GroupAlgebraicSpace (terminalSpace k) :=
  AlgebraicSpace.MultiplicativeGroup.groupSpace (terminalSpace k)

/-- The underlying object of `multiplicativeGroup k` is the multiplicative group algebraic space
over the terminal algebraic space. -/
theorem multiplicativeGroup_X (k : Type u) [Field k] :
    (multiplicativeGroup k).X =
      AlgebraicSpace.MultiplicativeGroup.asOver (terminalSpace k) :=
  sorry

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
      lift (actionPointGroup k T x) (actionPointSpace k T x) ≫ actionHom k p :=
  sorry

/-- Compatibility of `actionSmulLeft` with the structure morphisms over the terminal algebraic
space. -/
theorem actionSmul_w (k : Type u) [Field k] (p : ℕ) :
    actionSmulLeft k p ≫ (affineAsOver k).hom =
      ((multiplicativeGroup k).X ⊗ affineAsOver k).hom :=
  sorry

/-- The weighted action morphism in the slice over the terminal algebraic space. -/
def actionSmul (k : Type u) [Field k] (p : ℕ) :
    (multiplicativeGroup k).X ⊗ affineAsOver k ⟶ affineAsOver k :=
  Over.homMk (actionSmulLeft k p) (actionSmul_w k p)

/-- The underlying algebraic-space map of `actionSmul` is `actionSmulLeft`. -/
theorem actionSmul_left (k : Type u) [Field k] (p : ℕ) :
    (actionSmul k p).left = actionSmulLeft k p :=
  sorry

/-- The identity-action law for the algebraic-space weighted action. -/
theorem actionSmul_one_smul (k : Type u) [Field k] (p : ℕ) :
    η[(multiplicativeGroup k).X] ⊵ₗ affineAsOver k ≫ actionSmul k p =
      (λₗ (affineAsOver k)).hom :=
  sorry

/-- The multiplication-action law for the algebraic-space weighted action. -/
theorem actionSmul_mul_smul (k : Type u) [Field k] (p : ℕ) :
    μ[(multiplicativeGroup k).X] ⊵ₗ affineAsOver k ≫ actionSmul k p =
      (αₗ (multiplicativeGroup k).X (multiplicativeGroup k).X (affineAsOver k)).hom ≫
        (multiplicativeGroup k).X ⊴ₗ actionSmul k p ≫ actionSmul k p :=
  sorry

/-- The module-object structure of the weighted algebraic-space action. -/
@[reducible]
def actionModObj (k : Type u) [Field k] (p : ℕ) :
    ModObj (multiplicativeGroup k).X (affineAsOver k) where
  smul := actionSmul k p
  one_smul := actionSmul_one_smul k p
  mul_smul := actionSmul_mul_smul k p

/-- The stored algebraic-space action morphism is `actionSmul`. -/
theorem actionModObj_smul (k : Type u) [Field k] (p : ℕ) :
    (actionModObj k p).smul = actionSmul k p :=
  sorry

/-- The weighted action of `𝔾ₘ` on infinite affine space, as an action of a group algebraic
space. -/
def action (k : Type u) [Field k] (p : ℕ) (hp : Nat.Prime p) :
    GroupAlgebraicSpace.Action (multiplicativeGroup k) where
  X := affineAsOver k
  mod := actionModObj k p

/-- The object underlying `action` is infinite affine space over the terminal algebraic space. -/
theorem action_X (k : Type u) [Field k] (p : ℕ) (hp : Nat.Prime p) :
    (action k p hp).X = affineAsOver k :=
  sorry

/-- The stored action morphism of `action` is `actionSmul`. -/
theorem action_smul (k : Type u) [Field k] (p : ℕ) (hp : Nat.Prime p) :
    (action k p hp).mod.smul = actionSmul k p :=
  sorry

/-- The action groupoid of the weighted `𝔾ₘ`-action on infinite affine space. -/
def groupoid (k : Type u) [Field k] (p : ℕ) (hp : Nat.Prime p) :
    GroupoidAlgebraicSpace (terminalSpace k) :=
  GroupoidAlgebraicSpace.ofAction (multiplicativeGroup k) (action k p hp)

/-- The object space of the action groupoid is infinite affine space. -/
theorem groupoid_U (k : Type u) [Field k] (p : ℕ) (hp : Nat.Prime p) :
    (groupoid k p hp).U = affineAsOver k :=
  sorry

/-- The arrow space of the action groupoid is `𝔾ₘ × U`. -/
theorem groupoid_R (k : Type u) [Field k] (p : ℕ) (hp : Nat.Prime p) :
    (groupoid k p hp).R = (multiplicativeGroup k).X ⊗ affineAsOver k :=
  sorry

/-- The quotient stack `𝒳 = [U / 𝔾ₘ]` of the weighted action. -/
def stack (k : Type u) [Field k] (p : ℕ) (hp : Nat.Prime p) :
    GroupoidsOver (base k) :=
  (groupoid k p hp).quotientStack

/-- `stack k p hp` is the quotient stack of the weighted action groupoid. -/
theorem stack_eq (k : Type u) [Field k] (p : ℕ) (hp : Nat.Prime p) :
    stack k p hp = (groupoid k p hp).quotientStack :=
  sorry

/-- The quotient stack `[U / 𝔾ₘ]` of the weighted action is an algebraic stack. -/
instance instAlgebraicStack (k : Type u) [Field k] (p : ℕ) (hp : Nat.Prime p) :
    AlgebraicStack (stack k p hp) :=
  sorry

/-- The atlas `U ⟶ [U / 𝔾ₘ]` of the weighted quotient stack. -/
def atlas (k : Type u) [Field k] (p : ℕ) (hp : Nat.Prime p) :
    (AlgebraicSpace.ofOver (affineSpace k)).toGroupoids ⟶ stack k p hp :=
  (groupoid k p hp).atlas

/-- `atlas` is the atlas of the weighted action groupoid. -/
theorem atlas_eq (k : Type u) [Field k] (p : ℕ) (hp : Nat.Prime p) :
    atlas k p hp = (groupoid k p hp).atlas :=
  sorry

end AlgebraicGeometry.AlgebraicStack.WeightedInfiniteAffine
