/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.RingTheory.Finiteness.Basic

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.Deligne
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.Stalk.Constant

/-!
# Deligne data for the constant rank-one sheaf

The number field is the universe lift of `ℚ`, the polynomial at each closed
point is `T - 1`, and each companion is the continuous trivial representation
on a one-dimensional space. These are explicit data. The comparison laws refer
to the actual stalk and Frobenius of `ZEllSheaf.constant`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.SchemeOverField
open IsDedekindDomain Matrix
open scoped AlgebraicGeometry NumberField Polynomial

namespace AlgebraicGeometry.Scheme.Etale.ZEllSheaf

/-- The lifted rational field has its canonical number-field structure. -/
instance constantDeligneNumberField : NumberField (ULift.{u} ℚ) :=
  NumberField.of_ringEquiv ℚ (ULift.{u} ℚ)
    (ULift.ringEquiv : ULift.{u} ℚ ≃+* ℚ).symm

/-- The rational embedding into the coefficient field; no embedding is chosen. -/
def constantDeligneEmbedding (ℓ : ℕ) [Fact ℓ.Prime] :
    ULift.{u} ℚ →+* ℚ_[ℓ] :=
  (algebraMap ℚ ℚ_[ℓ]).comp ULift.ringEquiv.toRingHom

/-- The same explicit rank-one polynomial at every closed point. -/
def constantDelignePolynomial (X : Scheme.{u}) (_x : closedPoints X) :
    Polynomial (ULift.{u} ℚ) := Polynomial.X - 1

/-- Trivial continuous rank-one companions over each finite completion of `ℚ`.
This construction requires neither a characteristic nor a choice of Frobenius. -/
def constantDeligneCompanion {X : Scheme.{u}} (xbar : GeometricPoint X)
    (v : HeightOneSpectrum (𝓞 (ULift.{u} ℚ))) :
    ContinuousMonoidHom (etaleFundamentalGroup X xbar)
      (GL (Fin 1) (v.adicCompletion (ULift.{u} ℚ))) where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (one_mul 1).symm
  continuous_toFun := continuous_const

@[simp]
theorem constantDeligneEmbedding_up (ℓ : ℕ) [Fact ℓ.Prime] (a : ℚ) :
    constantDeligneEmbedding.{u} ℓ (ULift.up a) = algebraMap ℚ ℚ_[ℓ] a := rfl

@[simp]
theorem constantDelignePolynomial_eq (X : Scheme.{u}) (x : closedPoints X) :
    constantDelignePolynomial X x = Polynomial.X - 1 := rfl

@[simp]
theorem constantDeligneCompanion_apply {X : Scheme.{u}} (xbar : GeometricPoint X)
    (v : HeightOneSpectrum (𝓞 (ULift.{u} ℚ)))
    (g : etaleFundamentalGroup X xbar) :
    constantDeligneCompanion xbar v g = 1 := rfl

/-- Every complex embedding sends the only root of the displayed polynomial
to `1`, hence to a number of norm one. -/
theorem constantDelignePolynomial_root_norm (X : Scheme.{u}) (x : closedPoints X)
    (τ : ULift.{u} ℚ →+* ℂ) (α : ℂ)
    (hα : ((constantDelignePolynomial X x).map τ).IsRoot α) : ‖α‖ = 1 := by
  have h : α = 1 := by
    simpa only [constantDelignePolynomial, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_one, Polynomial.IsRoot, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_one, sub_eq_zero] using hα
  rw [h]
  simp

variable {k : Type u} [Field k] [Fintype k]
variable {ℓ : ℕ} [Fact ℓ.Prime]
variable {X : SchemeOverField k} [Scheme.Hom.FiniteType X.hom] [IsNoetherian X.left]
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]

/-- The stagewise Galois action fixes every element of the actual constant
stalk. This is the constant-fibre naturality law in stage coordinates. -/
theorem constant_componentStalkGaloisHom (x : closedPoints X.left)
    (σ : Gal(AlgebraicClosure (X.left.residueField x.1)/X.left.residueField x.1))
    (n : ℕ) :
    (constant X.left ℓ).componentStalkGaloisHom x σ n = 𝟙 _ := by
  sorry

/-- Geometric Frobenius on the integral constant stalk is the identity. -/
theorem constant_geometricFrobeniusStalkZEll (x : closedPoints X.left) :
    (constant X.left ℓ).geometricFrobeniusStalkZEll x = LinearMap.id := by
  have hstage := constant_componentStalkGaloisHom (ℓ := ℓ) x
  sorry

/-- Geometric Frobenius on the rational constant stalk is the identity. -/
theorem constant_geometricFrobeniusStalk (x : closedPoints X.left) :
    (constant X.left ℓ).geometricFrobeniusStalk x = LinearMap.id := by
  unfold geometricFrobeniusStalk
  rw [constant_geometricFrobeniusStalkZEll]
  change ModuleCat.Hom.hom
    ((ModuleCat.extendScalars (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map (𝟙 _)) = _
  erw [CategoryTheory.Functor.map_id]
  rfl

/-- In the explicit rational coordinates, Frobenius fixes the coordinate. -/
theorem constantQellStalkEquiv_frobenius (x : closedPoints X.left)
    (m : (constant X.left ℓ).qellStalk (geometricPointOverClosedPoint X x)) :
    constantQellStalkEquiv (geometricPointOverClosedPoint X x)
        ((constant X.left ℓ).geometricFrobeniusStalk x m) =
      constantQellStalkEquiv (geometricPointOverClosedPoint X x) m := by
  rw [constant_geometricFrobeniusStalk]
  rfl

/-- The polynomial `T - 1` is the characteristic polynomial of the actual
constant-sheaf Frobenius, via its explicit rank-one stalk coordinates. -/
theorem constantDelignePolynomial_map (x : closedPoints X.left) :
    (constantDelignePolynomial X.left x).map (constantDeligneEmbedding ℓ) =
      LinearMap.charpoly ((constant X.left ℓ).geometricFrobeniusStalk x) := by
  have hcoords := constantQellStalkEquiv (ℓ := ℓ) (geometricPointOverClosedPoint X x)
  have hfrob := constant_geometricFrobeniusStalk (ℓ := ℓ) x
  sorry

variable [ConnectedSpace X.left]

/-- The displayed trivial companion has precisely the displayed polynomial
at every transported closed-point Frobenius. -/
theorem constantDeligneCompanion_charpoly (xbar : GeometricPoint X.left)
    (v : HeightOneSpectrum (𝓞 (ULift.{u} ℚ))) (x : closedPoints X.left)
    (ιFrob : GeometricPoint.finiteFiber (geometricPointOverClosedPoint X x) ≅
      GeometricPoint.finiteFiber xbar) :
    (constantDelignePolynomial X.left x).map (NumberField.FinitePlace.embedding v) =
      Matrix.charpoly
        (constantDeligneCompanion xbar v (etaleGeometricFrobenius X xbar x ιFrob)).val := by
  rw [constantDeligneCompanion_apply]
  change (constantDelignePolynomial X.left x).map (NumberField.FinitePlace.embedding v) =
    Matrix.charpoly (1 : Matrix (Fin 1) (Fin 1) (v.adicCompletion (ULift.{u} ℚ)))
  simp [constantDelignePolynomial, Matrix.charpoly_one]

/-- The constant rank-one coefficient supplies Deligne's conclusions with
`ℚ`, the identity extension, `T - 1`, and continuous trivial companions.
A base point is used only as an existential witness in this Prop proof. -/
theorem constant_satisfiesDeligneConclusions (p : ℕ) :
    (constant X.left ℓ).SatisfiesDeligneConclusions (p := p) := by
  refine ⟨ULift.{u} ℚ, inferInstance, inferInstance, constantDeligneEmbedding ℓ, ?_, ?_⟩
  · intro x
    exact ⟨constantDelignePolynomial X.left x, constantDelignePolynomial_map x,
      constantDelignePolynomial_root_norm X.left x⟩
  · -- This elimination supplies only the base point in the Prop-valued packet.
    obtain ⟨x⟩ := (inferInstance : Nonempty X.left)
    let xbar : GeometricPoint X.left :=
      GeometricPoint.of (AlgebraicClosure (X.left.residueField x))
        (FieldExtension.specMap (X.left.residueField x)
          (AlgebraicClosure (X.left.residueField x)) ≫ X.left.fromSpecResidueField x)
    refine ⟨ULift.{u} ℚ, inferInstance, inferInstance, RingHom.id _, 1, xbar, ?_, ?_⟩
    · exact RingHom.Finite.id _
    · intro v hv
      refine ⟨constantDeligneCompanion xbar v, ?_⟩
      intro x ιFrob
      refine ⟨constantDelignePolynomial X.left x, constantDelignePolynomial_map x, ?_⟩
      simpa using constantDeligneCompanion_charpoly xbar v x ιFrob

end AlgebraicGeometry.Scheme.Etale.ZEllSheaf
