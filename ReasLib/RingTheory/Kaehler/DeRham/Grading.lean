/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Graded.HomogeneousMap
public import ReasLib.RingTheory.Kaehler.DeRham
public import ReasLib.RingTheory.Kaehler.DeRham.Wedge
public import Mathlib.Algebra.GradedMulAction
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# The grading on the de Rham complex of a graded ring

This file defines the homogeneous pieces of Kähler differentials and higher relative forms for a
graded algebra. It also records compatibility with the de Rham differential and wedge product.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

universe u v

namespace KaehlerDifferential.DeRham.Grading

variable {G : Type v} [DecidableEq G] [AddCommMonoid G]
variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : G → Submodule R A) [GradedAlgebra 𝒜]

/-- The degree-`g` submodule of `Ω[A⁄R]`, spanned by the forms `a₀ • D R A a₁` whose
coefficient and differentiated input are homogeneous of degrees summing to `g`. -/
def onePiece (g : G) : Submodule R Ω[A⁄R] :=
  Submodule.span R {ω | ∃ (g₀ g₁ : G) (a₀ a₁ : A),
    a₀ ∈ 𝒜 g₀ ∧ a₁ ∈ 𝒜 g₁ ∧ g₀ + g₁ = g ∧
      ω = a₀ • KaehlerDifferential.D R A a₁}

/-- A homogeneous basic one-form belongs to the piece indexed by the sum of its two degrees. -/
theorem oneBasic_mem {g₀ g₁ g : G} {a₀ a₁ : A}
    (ha₀ : a₀ ∈ 𝒜 g₀) (ha₁ : a₁ ∈ 𝒜 g₁) (hdeg : g₀ + g₁ = g) :
    a₀ • KaehlerDifferential.D R A a₁ ∈ onePiece R A 𝒜 g := by
  exact Submodule.subset_span ⟨g₀, g₁, a₀, a₁, ha₀, ha₁, hdeg, rfl⟩

/-- The degree-`g` submodule of relative `p`-forms, spanned by homogeneous basic forms whose
coefficient degree plus the degrees of their differential inputs is `g`. -/
def piece (p : ℕ) (g : G) : Submodule R (term R A p) :=
  Submodule.span R {ω | ∃ (g₀ : G) (gs : Fin p → G) (a₀ : A) (a : Fin p → A),
    a₀ ∈ 𝒜 g₀ ∧ (∀ i, a i ∈ 𝒜 (gs i)) ∧
      g₀ + ∑ i, gs i = g ∧ ω = basic R A p a₀ a}

/-- A homogeneous basic `p`-form belongs to the piece indexed by its total input degree. -/
theorem basic_mem {p : ℕ} {g₀ g : G} {gs : Fin p → G} {a₀ : A} {a : Fin p → A}
    (ha₀ : a₀ ∈ 𝒜 g₀) (ha : ∀ i, a i ∈ 𝒜 (gs i))
    (hdeg : g₀ + ∑ i, gs i = g) :
    basic R A p a₀ a ∈ piece R A 𝒜 p g := by
  exact Submodule.subset_span ⟨g₀, gs, a₀, a, ha₀, ha, hdeg, rfl⟩

/-- The underlying function of the canonical comparison from presented one-forms to Kähler
differentials. -/
def toOneFormFun (x : term R A 1) : Ω[A⁄R] :=
  toExterior R A 1 x

/-- Additivity of the canonical comparison from presented one-forms to Kähler differentials. -/
theorem toOneForm_add (x y : term R A 1) :
    toOneFormFun R A (x + y) = toOneFormFun R A x + toOneFormFun R A y := by
  exact (toExterior R A 1).hom.map_add x y

/-- `R`-linearity of the canonical comparison from presented one-forms to Kähler differentials. -/
theorem toOneForm_smul (r : R) (x : term R A 1) :
    toOneFormFun R A (r • x) = r • toOneFormFun R A x := by
  calc
    toOneFormFun R A (r • x) = algebraMap R A r • toOneFormFun R A x :=
      (toExterior R A 1).hom.map_smul (algebraMap R A r) (show Form R A 1 from x)
    _ = r • toOneFormFun R A x := algebraMap_smul A r _

/-- The canonical `R`-linear comparison from presented one-forms to Kähler differentials. -/
def toOneForm : term R A 1 →ₗ[R] Ω[A⁄R] where
  toFun := toOneFormFun R A
  map_add' := toOneForm_add R A
  map_smul' := toOneForm_smul R A

/-- The direct Kähler-differential grading agrees with the degree-one presented-form grading under
the canonical comparison map. -/
theorem onePiece_eq_map_piece_one (g : G) :
    onePiece R A 𝒜 g = (piece R A 𝒜 1 g).map (toOneForm R A) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨g₀, g₁, a₀, a₁, ha₀, ha₁, hdeg, rfl⟩
    refine ⟨basic R A 1 a₀ (fun _ ↦ a₁),
      basic_mem R A 𝒜 ha₀ (fun _ ↦ ha₁) (by simpa using hdeg), ?_⟩
    change toExterior R A 1 (basic R A 1 a₀ (fun _ ↦ a₁)) = _
    rw [toExterior_basic]
    rfl
  · rw [piece, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨g₀, gs, a₀, a, ha₀, ha, hdeg, rfl⟩, rfl⟩
    change toExterior R A 1 (basic R A 1 a₀ a) ∈ onePiece R A 𝒜 g
    rw [toExterior_basic]
    exact oneBasic_mem R A 𝒜 ha₀ (ha 0) (by simpa using hdeg)

/-- The homogeneous pieces of `Ω[A⁄R]` form an internal direct sum. -/
theorem onePiece_isInternal : DirectSum.IsInternal (onePiece R A 𝒜) := sorry

/-- For every `p`, the homogeneous pieces of relative `p`-forms form an internal direct sum. -/
theorem piece_isInternal (p : ℕ) : DirectSum.IsInternal (piece R A 𝒜 p) := sorry

/-- The graded algebra action on relative `p`-forms respects the homogeneous pieces. -/
instance instGradedSMulPiece (p : ℕ) : SetLike.GradedSMul 𝒜 (piece R A 𝒜 p) where
  smul_mem := by
    intro g h a x ha hx
    change a • x ∈ piece R A 𝒜 p (g + h)
    let f : term R A p →ₗ[R] term R A p :=
      ((ModuleCat.restrictScalars (algebraMap R A)).map
        (ModuleCat.ofHom (X := form R A p) (Y := form R A p)
          (a • (LinearMap.id : Form R A p →ₗ[A] Form R A p)))).hom
    refine (Submodule.span_le.mpr ?_ : piece R A 𝒜 p h ≤
      (piece R A 𝒜 p (g + h)).comap f) hx
    rintro _ ⟨g₀, gs, a₀, bs, ha₀, hbs, hdeg, rfl⟩
    have hf : f (basic R A p a₀ bs) = basic R A p (a * a₀) bs := by
      change (a • basic R A p a₀ bs : Form R A p) = _
      rw [basic_eq_smul_exact, smul_smul, ← basic_eq_smul_exact]
    change f (basic R A p a₀ bs) ∈ piece R A 𝒜 p (g + h)
    rw [hf]
    exact basic_mem R A 𝒜 (SetLike.mul_mem_graded ha ha₀) hbs
      (by rw [add_assoc, hdeg])

/-- The de Rham differential sends a homogeneous form to the piece of the same grading degree. -/
theorem d_mem {p : ℕ} {g : G} {x : term R A p} (hx : x ∈ piece R A 𝒜 p g) :
    d R A p x ∈ piece R A 𝒜 (p + 1) g := by
  refine (Submodule.span_le.mpr ?_ : piece R A 𝒜 p g ≤
    (piece R A 𝒜 (p + 1) g).comap (d R A p).hom) hx
  rintro _ ⟨g₀, gs, a₀, a, ha₀, ha, hdeg, rfl⟩
  change d R A p (basic R A p a₀ a) ∈ piece R A 𝒜 (p + 1) g
  have hd : d R A p (basic R A p a₀ a) =
      basic R A (p + 1) 1 (Fin.cons a₀ a) := by
    change termLinearEquiv R A (p + 1)
      ((target R A p).hom (Finsupp.single (a₀, a) 1)) = _
    change termLinearEquiv R A (p + 1)
      (Finsupp.lsum R (coefficientTarget R A p) (Finsupp.single (a₀, a) 1)) = _
    rw [Finsupp.lsum_single]
    simp [coefficientTarget, aExact, aBasic, termLinearEquiv, basic, quotient]
  rw [hd]
  exact basic_mem R A 𝒜 (g₀ := 0) (gs := Fin.cons g₀ gs)
    (SetLike.one_mem_graded 𝒜) (fun i ↦ Fin.cases ha₀ ha i)
    (by simpa [Fin.sum_univ_succ] using hdeg)

/-- The de Rham differential bundled as a linear map preserving the grading degree. -/
def dHom (p : ℕ) :
    GradedModule.MapsTo R (piece R A 𝒜 p) (piece R A 𝒜 (p + 1)) (fun g ↦ g) :=
  ⟨(d R A p).hom, fun _ _ hx ↦ d_mem R A 𝒜 hx⟩

/-- The underlying linear map of `dHom` is the canonical de Rham differential. -/
theorem dHom_toLinearMap (p : ℕ) :
    GradedModule.MapsTo.toLinearMap (dHom R A 𝒜 p) = (d R A p).hom := rfl

/-- Wedge multiplication adds the grading degrees of two homogeneous forms. -/
theorem wedge_mem {p q : ℕ} {g h : G} {x : term R A p} {y : term R A q}
    (hx : x ∈ piece R A 𝒜 p g) (hy : y ∈ piece R A 𝒜 q h) :
    formWedgeBilinear R A p q x y ∈ piece R A 𝒜 (p + q) (g + h) := by
  refine (Submodule.span_le.mpr ?_ : piece R A 𝒜 p g ≤
    (piece R A 𝒜 (p + q) (g + h)).comap
      (((ModuleCat.restrictScalars (algebraMap R A)).map
        (ModuleCat.ofHom (X := form R A p) (Y := form R A (p + q))
          ((formWedgeBilinear R A p q).flip y))).hom)) hx
  rintro _ ⟨g₀, gs, a₀, a, ha₀, ha, hdeg, rfl⟩
  change formWedgeBilinear R A p q (basic R A p a₀ a) y ∈
    piece R A 𝒜 (p + q) (g + h)
  refine (Submodule.span_le.mpr ?_ : piece R A 𝒜 q h ≤
    (piece R A 𝒜 (p + q) (g + h)).comap
      (((ModuleCat.restrictScalars (algebraMap R A)).map
        (ModuleCat.ofHom (X := form R A q) (Y := form R A (p + q))
          (formWedgeBilinear R A p q (basic R A p a₀ a)))).hom)) hy
  rintro _ ⟨h₀, hs, b₀, b, hb₀, hb, hdeg', rfl⟩
  change formWedgeBilinear R A p q (basic R A p a₀ a) (basic R A q b₀ b) ∈
    piece R A 𝒜 (p + q) (g + h)
  have hw : formWedgeBilinear R A p q (basic R A p a₀ a) (basic R A q b₀ b) =
      basic R A (p + q) (a₀ * b₀) (Fin.append a b) := by
    change freeWedgeFun R A p q
      (Finsupp.single (a₀, a) 1) (Finsupp.single (b₀, b) 1) = _
    simp [freeWedgeFun]
  rw [hw]
  refine basic_mem R A 𝒜 (SetLike.mul_mem_graded ha₀ hb₀)
    (gs := Fin.append gs hs) ?_ ?_
  · intro i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simpa only [Fin.append_left] using ha j
    · simpa only [Fin.append_right] using hb j
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [← hdeg, ← hdeg']
    abel

end KaehlerDifferential.DeRham.Grading
