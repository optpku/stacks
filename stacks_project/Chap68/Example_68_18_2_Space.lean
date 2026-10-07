module

public import Mathlib.GroupTheory.OrderOfElement
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientPresheaf
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.Functoriality
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap68.Example_68_18_2_Presentation

/-!
# Algebraic spaces Spec(K)/ℤ and 𝔸¹_K/ℤ

This module packages the quotient presheaves of the two étale relations from
`Example_68_18_2_Presentation` as algebraic spaces over `Spec(ULift ℤ)`, together with the
four maps of the source cartesian square.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.InfiniteOrderFibre

/-- The algebraic space `Y = Spec(K)/ℤ` over `Spec(ULift ℤ)`, presented by the action of
powers of `σ`. -/
def Y (K : Type u) [Field K] [CharZero K] (σ : RingAut K) (hσ : ¬ IsOfFinOrder σ) :
    AlgebraicSpace (base.{u}) where
  functorOfPoints := (specRelation K σ).quotientPresheaf
  isSheaf := sorry
  representableDiagonal := sorry
  atlas := ⟨specOver K, (specRelation K σ).quotientMk, sorry, sorry⟩

/-- The functor of points of `Y` is the objectwise quotient of `T`-points of `Spec(K)` by
powers of `σ`. -/
theorem Y_functorOfPoints (K : Type u) [Field K] [CharZero K] (σ : RingAut K)
    (hσ : ¬ IsOfFinOrder σ) :
    (Y K σ hσ).functorOfPoints = (specRelation K σ).quotientPresheaf := sorry

/-- The atlas `Spec(K) ⟶ Spec(K)/ℤ` is the canonical projection to the quotient presheaf. -/
def atlasY (K : Type u) [Field K] [CharZero K] (σ : RingAut K) (hσ : ¬ IsOfFinOrder σ) :
    yoneda.obj (specOver K) ⟶ (Y K σ hσ).functorOfPoints :=
  (specRelation K σ).quotientMk

/-- The atlas of `Y` is the quotient projection of the spec pre-relation. -/
theorem atlasY_eq (K : Type u) [Field K] [CharZero K] (σ : RingAut K)
    (hσ : ¬ IsOfFinOrder σ) :
    atlasY K σ hσ = (specRelation K σ).quotientMk := sorry

/-- The algebraic space `X = 𝔸¹_K/ℤ` over `Spec(ULift ℤ)`, presented by translation together
with the coefficient action of `σ`. -/
def X (K : Type u) [Field K] [CharZero K] (σ : RingAut K) : AlgebraicSpace (base.{u}) where
  functorOfPoints := (affineRelation K σ).quotientPresheaf
  isSheaf := sorry
  representableDiagonal := sorry
  atlas := ⟨affineOver K, (affineRelation K σ).quotientMk, sorry, sorry⟩

/-- The functor of points of `X` is the objectwise quotient of `T`-points of `𝔸¹_K` by the
combined `ℤ`-action. -/
theorem X_functorOfPoints (K : Type u) [Field K] [CharZero K] (σ : RingAut K) :
    (X K σ).functorOfPoints = (affineRelation K σ).quotientPresheaf := sorry

/-- The atlas `𝔸¹_K ⟶ 𝔸¹_K/ℤ` is the canonical projection to the quotient presheaf. -/
def atlasX (K : Type u) [Field K] [CharZero K] (σ : RingAut K) :
    yoneda.obj (affineOver K) ⟶ (X K σ).functorOfPoints :=
  (affineRelation K σ).quotientMk

/-- The atlas of `X` is the quotient projection of the affine pre-relation. -/
theorem atlasX_eq (K : Type u) [Field K] [CharZero K] (σ : RingAut K) :
    atlasX K σ = (affineRelation K σ).quotientMk := sorry

/-- The algebraic space `Z = Spec(K)` over `Spec(ULift ℤ)`. -/
def Z (K : Type u) [Field K] [CharZero K] : AlgebraicSpace (base.{u}) :=
  ofOver (specOver K)

/-- `Z` is the algebraic space represented by `specOver K`. -/
theorem Z_eq (K : Type u) [Field K] [CharZero K] : Z K = ofOver (specOver K) := sorry

/-- The functor of points of `Z` is the representable presheaf of `Spec(K)`. -/
theorem Z_functorOfPoints (K : Type u) [Field K] [CharZero K] :
    (Z K).functorOfPoints = yoneda.obj (specOver K) := sorry

/-- The algebraic space `W = 𝔸¹_K` over `Spec(ULift ℤ)`. -/
def W (K : Type u) [Field K] [CharZero K] : AlgebraicSpace (base.{u}) :=
  ofOver (affineOver K)

/-- `W` is the algebraic space represented by `affineOver K`. -/
theorem W_eq (K : Type u) [Field K] [CharZero K] : W K = ofOver (affineOver K) := sorry

/-- The functor of points of `W` is the representable presheaf of `𝔸¹_K`. -/
theorem W_functorOfPoints (K : Type u) [Field K] [CharZero K] :
    (W K).functorOfPoints = yoneda.obj (affineOver K) := sorry

/-- The atlas morphism `p : 𝔸¹_K ⟶ 𝔸¹_K/ℤ`. -/
def p (K : Type u) [Field K] [CharZero K] (σ : RingAut K) : W K ⟶ X K σ :=
  (affineRelation K σ).quotientMk

/-- `p` is the quotient projection of the affine pre-relation. -/
theorem p_eq (K : Type u) [Field K] [CharZero K] (σ : RingAut K) :
    p K σ = (affineRelation K σ).quotientMk := sorry

/-- The atlas morphism `g : Spec(K) ⟶ Spec(K)/ℤ`. -/
def g (K : Type u) [Field K] [CharZero K] (σ : RingAut K) (hσ : ¬ IsOfFinOrder σ) :
    Z K ⟶ Y K σ hσ :=
  (specRelation K σ).quotientMk

/-- `g` is the quotient projection of the spec pre-relation. -/
theorem g_eq (K : Type u) [Field K] [CharZero K] (σ : RingAut K) (hσ : ¬ IsOfFinOrder σ) :
    g K σ hσ = (specRelation K σ).quotientMk := sorry

/-- The structure morphism `q : 𝔸¹_K ⟶ Spec(K)` of algebraic spaces over `Spec(ULift ℤ)`. -/
def q (K : Type u) [Field K] [CharZero K] : W K ⟶ Z K :=
  ofOverMap (structureHom K)

/-- `q` is `ofOverMap` of the affine-line projection. -/
theorem q_eq (K : Type u) [Field K] [CharZero K] :
    q K = ofOverMap (structureHom K) := sorry

/-- The induced morphism `f : 𝔸¹_K/ℤ ⟶ Spec(K)/ℤ` of quotient algebraic spaces. -/
def f (K : Type u) [Field K] [CharZero K] (σ : RingAut K) (hσ : ¬ IsOfFinOrder σ) :
    X K σ ⟶ Y K σ hσ :=
  (relationHom K σ).quotientPresheafMap

/-- `f` is the map of quotient presheaves induced by `relationHom`. -/
theorem f_eq (K : Type u) [Field K] [CharZero K] (σ : RingAut K) (hσ : ¬ IsOfFinOrder σ) :
    f K σ hσ = (relationHom K σ).quotientPresheafMap := sorry

/-- The square `W ⟶ Z` over `X ⟶ Y` commutes. -/
theorem comm_sq (K : Type u) [Field K] [CharZero K] (σ : RingAut K) (hσ : ¬ IsOfFinOrder σ) :
    q K ≫ g K σ hσ = p K σ ≫ f K σ hσ := sorry

end AlgebraicGeometry.AlgebraicSpace.InfiniteOrderFibre
