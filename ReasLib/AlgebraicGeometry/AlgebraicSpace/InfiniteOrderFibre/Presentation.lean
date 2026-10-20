module

public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Ring.Aut
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Logic.Basic
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.Over
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Hom
public import ReasLib.AlgebraicGeometry.Scheme.EtaleEquivalenceRelation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient.Presentation

/-!
# Affine line and Spec(K) modulo a ℤ-action

This module records the common base `Spec(ULift ℤ)`, the objects `Spec(K)` and `𝔸¹_K` over that
base, the action of an automorphism `σ` together with integer translation, and the two étale
equivalence relations presenting `Spec(K)/ℤ` and `𝔸¹_K/ℤ`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits AffineSpace
open AlgebraicGeometry.Scheme
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.InfiniteOrderFibre

/-- The common base scheme `S = Spec(ULift ℤ)`. -/
abbrev base : Scheme.{u} :=
  Spec (CommRingCat.of (ULift.{u} ℤ))

/-- The spectrum of a characteristic-zero field `K`. -/
abbrev specK (K : Type u) [Field K] [CharZero K] : Scheme.{u} :=
  Spec (CommRingCat.of K)

/-- The affine line `𝔸¹_K`. -/
abbrev affineLine (K : Type u) [Field K] [CharZero K] : Scheme.{u} :=
  𝔸(ULift.{u} (Fin 1); specK K)

/-- The structure morphism `Spec(K) ⟶ Spec(ULift ℤ)` induced by `ULift ℤ → K`. -/
def specToBase (K : Type u) [Field K] [CharZero K] : specK K ⟶ base.{u} :=
  Spec.map (CommRingCat.ofHom ((Int.castRingHom K).comp ULift.ringEquiv.toRingHom))

/-- The scheme `Spec(K)` as an object over `Spec(ULift ℤ)`. -/
def specOver (K : Type u) [Field K] [CharZero K] : Over (base.{u}) :=
  Over.mk (specToBase K)

/-- The underlying scheme of `specOver K` is `Spec(K)`. -/
theorem specOver_left (K : Type u) [Field K] [CharZero K] :
    (specOver K).left = specK K := rfl

/-- The structure morphism of `specOver K` is `specToBase K`. -/
theorem specOver_hom (K : Type u) [Field K] [CharZero K] :
    (specOver K).hom = specToBase K := rfl

/-- The scheme `𝔸¹_K` as an object over `Spec(ULift ℤ)`. -/
def affineOver (K : Type u) [Field K] [CharZero K] : Over (base.{u}) :=
  Over.mk (affineLine K ↘ specK K ≫ specToBase K)

/-- The underlying scheme of `affineOver K` is the affine line over `K`. -/
theorem affineOver_left (K : Type u) [Field K] [CharZero K] :
    (affineOver K).left = affineLine K := rfl

/-- The structure morphism of `affineOver K` is the composite through `Spec(K)`. -/
theorem affineOver_hom (K : Type u) [Field K] [CharZero K] :
    (affineOver K).hom = affineLine K ↘ specK K ≫ specToBase K := rfl

/-- The affine-line projection `𝔸¹_K ⟶ Spec(K)` is compatible with the two structure morphisms
over `Spec(ULift ℤ)`. -/
theorem structureHom_w (K : Type u) [Field K] [CharZero K] :
    (affineLine K ↘ specK K) ≫ (specOver K).hom = (affineOver K).hom := rfl

/-- The structure morphism `𝔸¹_K ⟶ Spec(K)` as a morphism over `Spec(ULift ℤ)`. -/
def structureHom (K : Type u) [Field K] [CharZero K] :
    affineOver K ⟶ specOver K :=
  Over.homMk (affineLine K ↘ specK K) (structureHom_w K)

/-- The underlying scheme morphism of `structureHom K` is the affine-line projection. -/
theorem structureHom_left (K : Type u) [Field K] [CharZero K] :
    (structureHom K).left = affineLine K ↘ specK K := rfl

/-- The underlying scheme morphism of the `n`-th power of `σ`. -/
def specActLeft (K : Type u) [Field K] [CharZero K] (σ : RingAut K) (n : ℤ) :
    specK K ⟶ specK K :=
  Spec.map (CommRingCat.ofHom (σ ^ n).toRingHom)

/-- Powers of `σ` are morphisms over `Spec(ULift ℤ)`. -/
theorem specAct_w (K : Type u) [Field K] [CharZero K] (σ : RingAut K) (n : ℤ) :
    specActLeft K σ n ≫ specToBase K = specToBase K := sorry

/-- The automorphism `σ ^ n` as an endomorphism of `Spec(K)` over `Spec(ULift ℤ)`. -/
def specAct (K : Type u) [Field K] [CharZero K] (σ : RingAut K) (n : ℤ) :
    specOver K ⟶ specOver K :=
  Over.homMk (specActLeft K σ n) (specAct_w K σ n)

/-- The underlying scheme morphism of `specAct K σ n` is `specActLeft K σ n`. -/
theorem specAct_left (K : Type u) [Field K] [CharZero K] (σ : RingAut K) (n : ℤ) :
    (specAct K σ n).left = specActLeft K σ n := rfl

/-- The zero power of `σ` acts as the identity on `Spec(K)`. -/
theorem specAct_zero (K : Type u) [Field K] [CharZero K] (σ : RingAut K) :
    specAct K σ 0 = 𝟙 (specOver K) := sorry

/-- The action of powers of `σ` is a homomorphism from `(ℤ, +)`. -/
theorem specAct_add (K : Type u) [Field K] [CharZero K] (σ : RingAut K) (m n : ℤ) :
    specAct K σ (m + n) = specAct K σ m ≫ specAct K σ n := sorry

/-- The action of `σ ^ n` is inverted by `σ ^ (-n)`. -/
theorem specAct_neg (K : Type u) [Field K] [CharZero K] (σ : RingAut K) (n : ℤ) :
    specAct K σ n ≫ specAct K σ (-n) = 𝟙 (specOver K) := sorry

/-- The combined action on `𝔸¹_K`: apply `σ ^ n` to coefficients, then translate `t ↦ t + n`. -/
def affineActLeft (K : Type u) [Field K] [CharZero K] (σ : RingAut K) (n : ℤ) :
    affineLine K ⟶ affineLine K :=
  AffineSpace.map (ULift.{u} (Fin 1)) (specActLeft K σ n) ≫ AffineLineQuotient.translateLeft K n

/-- The combined action is a morphism of `𝔸¹_K` over `Spec(ULift ℤ)`. -/
theorem affineAct_w (K : Type u) [Field K] [CharZero K] (σ : RingAut K) (n : ℤ) :
    affineActLeft K σ n ≫ (affineOver K).hom = (affineOver K).hom := sorry

/-- The combined `σ`-and-translation action as an endomorphism of `𝔸¹_K` over `Spec(ULift ℤ)`. -/
def affineAct (K : Type u) [Field K] [CharZero K] (σ : RingAut K) (n : ℤ) :
    affineOver K ⟶ affineOver K :=
  Over.homMk (affineActLeft K σ n) (affineAct_w K σ n)

/-- The underlying scheme morphism of `affineAct K σ n` is `affineActLeft K σ n`. -/
theorem affineAct_left (K : Type u) [Field K] [CharZero K] (σ : RingAut K) (n : ℤ) :
    (affineAct K σ n).left = affineActLeft K σ n := rfl

/-- The zero action on the affine line is the identity. -/
theorem affineAct_zero (K : Type u) [Field K] [CharZero K] (σ : RingAut K) :
    affineAct K σ 0 = 𝟙 (affineOver K) := sorry

/-- The combined action is a homomorphism from `(ℤ, +)`. -/
theorem affineAct_add (K : Type u) [Field K] [CharZero K] (σ : RingAut K) (m n : ℤ) :
    affineAct K σ (m + n) = affineAct K σ m ≫ affineAct K σ n := sorry

/-- The structure morphism `𝔸¹_K ⟶ Spec(K)` is equivariant for the two `ℤ`-actions. -/
theorem structureHom_equivariant (K : Type u) [Field K] [CharZero K] (σ : RingAut K) (n : ℤ) :
    affineAct K σ n ≫ structureHom K = structureHom K ≫ specAct K σ n := sorry

/-- The `n`-th summand of the relation on `Spec(K)` is a copy of `Spec(K)`. -/
def specRelationComponent (K : Type u) [Field K] [CharZero K] : ℤ → Over (base.{u}) :=
  fun _ ↦ specOver K

/-- The component of the spec relation on the summand indexed by `n` is `(σ ^ n, id)`. -/
def specRelationComponentHom (K : Type u) [Field K] [CharZero K] (σ : RingAut K) (n : ℤ) :
    specRelationComponent K n ⟶ specOver K ⨯ specOver K :=
  prod.lift (specAct K σ n) (𝟙 (specOver K))

/-- The relation scheme `∐_{n : ℤ} Spec(K)` as an object over `Spec(ULift ℤ)`. -/
def specRelationOver (K : Type u) [Field K] [CharZero K] : Over (base.{u}) :=
  ∐ specRelationComponent K

/-- The morphism `j : ∐_n Spec(K) ⟶ Spec(K) ×_S Spec(K)` sending `(n, z)` to `(σ ^ n (z), z)`. -/
def specRelationHom (K : Type u) [Field K] [CharZero K] (σ : RingAut K) :
    specRelationOver K ⟶ specOver K ⨯ specOver K :=
  Sigma.desc (specRelationComponentHom K σ)

/-- The pre-relation on `Spec(K)` over `S` with source `∐_n Spec(K)` and defining map `j`. -/
def specRelation (K : Type u) [Field K] [CharZero K] (σ : RingAut K) :
    PreRelation (specOver K) :=
  PreRelation.ofHom (specRelationHom K σ)

/-- The first projection of the spec relation, restricted to the `n`-th summand, is `σ ^ n`. -/
theorem specRelation_t_ι (K : Type u) [Field K] [CharZero K] (σ : RingAut K) (n : ℤ) :
    Sigma.ι (specRelationComponent K) n ≫ (specRelation K σ).t = specAct K σ n := sorry

/-- The second projection of the spec relation, restricted to the `n`-th summand, is the
identity. -/
theorem specRelation_s_ι (K : Type u) [Field K] [CharZero K] (σ : RingAut K) (n : ℤ) :
    Sigma.ι (specRelationComponent K) n ≫ (specRelation K σ).s = 𝟙 (specOver K) := sorry

/-- The `ℤ`-action by powers of an infinite-order automorphism `σ` is an étale
equivalence relation on `Spec(K)`. -/
instance instIsEtaleEquivalenceRelation_specRelation
    (K : Type u) [Field K] [CharZero K] (σ : RingAut K) [hσ : Fact (¬ IsOfFinOrder σ)] :
    (specRelation K σ).IsEtaleEquivalenceRelation := sorry

/-- The `n`-th summand of the relation on `𝔸¹_K` is a copy of `𝔸¹_K`. -/
def affineRelationComponent (K : Type u) [Field K] [CharZero K] : ℤ → Over (base.{u}) :=
  fun _ ↦ affineOver K

/-- The component of the affine relation on the summand indexed by `n` is `(affineAct n, id)`. -/
def affineRelationComponentHom (K : Type u) [Field K] [CharZero K] (σ : RingAut K) (n : ℤ) :
    affineRelationComponent K n ⟶ affineOver K ⨯ affineOver K :=
  prod.lift (affineAct K σ n) (𝟙 (affineOver K))

/-- The relation scheme `∐_{n : ℤ} 𝔸¹_K` as an object over `Spec(ULift ℤ)`. -/
def affineRelationOver (K : Type u) [Field K] [CharZero K] : Over (base.{u}) :=
  ∐ affineRelationComponent K

/-- The morphism `j : ∐_n 𝔸¹_K ⟶ 𝔸¹_K ×_S 𝔸¹_K` sending `(n, w)` to `(n · w, w)`. -/
def affineRelationHom (K : Type u) [Field K] [CharZero K] (σ : RingAut K) :
    affineRelationOver K ⟶ affineOver K ⨯ affineOver K :=
  Sigma.desc (affineRelationComponentHom K σ)

/-- The pre-relation on `𝔸¹_K` over `S` with source `∐_n 𝔸¹_K` and defining map `j`. -/
def affineRelation (K : Type u) [Field K] [CharZero K] (σ : RingAut K) :
    PreRelation (affineOver K) :=
  PreRelation.ofHom (affineRelationHom K σ)

/-- The first projection of the affine relation, restricted to the `n`-th summand, is the
combined action. -/
theorem affineRelation_t_ι (K : Type u) [Field K] [CharZero K] (σ : RingAut K) (n : ℤ) :
    Sigma.ι (affineRelationComponent K) n ≫ (affineRelation K σ).t = affineAct K σ n := sorry

/-- The second projection of the affine relation, restricted to the `n`-th summand, is the
identity. -/
theorem affineRelation_s_ι (K : Type u) [Field K] [CharZero K] (σ : RingAut K) (n : ℤ) :
    Sigma.ι (affineRelationComponent K) n ≫ (affineRelation K σ).s = 𝟙 (affineOver K) := sorry

/-- Integer translation together with the coefficient action of `σ` is an étale equivalence
relation on `𝔸¹_K`. -/
instance instIsEtaleEquivalenceRelation_affineRelation
    (K : Type u) [Field K] [CharZero K] (σ : RingAut K) :
    (affineRelation K σ).IsEtaleEquivalenceRelation := sorry

/-- The coproduct of the structure maps `𝔸¹_K ⟶ Spec(K)` is a map of relation schemes. -/
def relationArrow (K : Type u) [Field K] [CharZero K] :
    affineRelationOver K ⟶ specRelationOver K :=
  Limits.Sigma.map fun _ : ℤ ↦ structureHom K

/-- The structure morphism of `𝔸¹_K` is compatible with the two defining maps of the
pre-relations. -/
theorem relationHom_map_hom (K : Type u) [Field K] [CharZero K] (σ : RingAut K) :
    (affineRelation K σ).hom ≫ prod.map (structureHom K) (structureHom K) =
      relationArrow K ≫ (specRelation K σ).hom := sorry

/-- The morphism of pre-relations induced by `𝔸¹_K ⟶ Spec(K)`, equivariant for the two
`ℤ`-actions. -/
def relationHom (K : Type u) [Field K] [CharZero K] (σ : RingAut K) :
    PreRelation.Hom (affineRelation K σ) (specRelation K σ) :=
  PreRelation.Hom.ofDefiningMap (structureHom K) (relationArrow K) (relationHom_map_hom K σ)

/-- The object map of `relationHom` is the structure morphism `𝔸¹_K ⟶ Spec(K)`. -/
theorem relationHom_obj (K : Type u) [Field K] [CharZero K] (σ : RingAut K) :
    (relationHom K σ).obj = structureHom K := rfl

/-- The arrow map of `relationHom` is the coproduct of the structure morphisms. -/
theorem relationHom_arrow (K : Type u) [Field K] [CharZero K] (σ : RingAut K) :
    (relationHom K σ).arrow = relationArrow K := rfl

end AlgebraicGeometry.AlgebraicSpace.InfiniteOrderFibre
