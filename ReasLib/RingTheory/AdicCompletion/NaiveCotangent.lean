/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Module.PUnit
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReasLib.RingTheory.AdicCompletion.AlgebraMap

/-!
# Completed naive cotangent complexes

This leaf owns the two-term Jacobian complex attached to a presentation of an
`A`-algebra as a quotient of an `I`-adic completed polynomial ring `A[x_ι]^∧`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace Algebra.NaiveCotangent.Adic

/-- The extended ideal `I · A[x_ι]` along which `A[x_ι]` is completed. -/
abbrev polynomialIdeal (A : Type u) [CommRing A] (I : Ideal A) (ι : Type u) :
    Ideal (MvPolynomial ι A) :=
  AdicCompletion.extensionIdeal I

/-- The extended ideal is the image of `I` in `A[x_ι]`. -/
theorem polynomialIdeal_eq_map (A : Type u) [CommRing A] (I : Ideal A) (ι : Type u) :
    polynomialIdeal A I ι = I.map (algebraMap A (MvPolynomial ι A)) := rfl

/-- The `I`-adic completion `A[x_ι]^∧` of a polynomial ring, taken along the
extended ideal `I · A[x_ι]`. -/
abbrev polynomialCompletion (A : Type u) [CommRing A] (I : Ideal A) (ι : Type u) : Type u :=
  AdicCompletion (polynomialIdeal A I ι) (MvPolynomial ι A)

/-- The completed polynomial ring is the adic completion of `A[x_ι]` along
`I · A[x_ι]`. -/
theorem polynomialCompletion_def (A : Type u) [CommRing A] (I : Ideal A) (ι : Type u) :
    polynomialCompletion A I ι =
      AdicCompletion (polynomialIdeal A I ι) (MvPolynomial ι A) := rfl

/-- A presentation of an `A`-algebra `B` as a quotient of an `I`-adic completed
polynomial ring `A[x_ι]^∧`. -/
structure Presentation (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (ι : Type u) where
  /-- The structure map `A[x_ι]^∧ →ₐ[A] B`. -/
  toAlgHom : polynomialCompletion A I ι →ₐ[A] B
  /-- The structure map is surjective. -/
  surjective : Function.Surjective toAlgHom

namespace Presentation

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {I : Ideal A} {ι : Type u}

/-- The quotient presentation `B = A[x_ι]^∧ / J`. -/
def ofQuotient (J : Ideal (polynomialCompletion A I ι)) :
    Presentation A (polynomialCompletion A I ι ⧸ J) I ι where
  toAlgHom := Ideal.Quotient.mkₐ A J
  surjective := Ideal.Quotient.mk_surjective

/-- Bundle a surjective map out of `A[x_ι]^∧` as a completed polynomial presentation. -/
def ofSurjective (f : polynomialCompletion A I ι →ₐ[A] B) (hf : Function.Surjective f) :
    Presentation A B I ι where
  toAlgHom := f
  surjective := hf

variable (P : Presentation A B I ι)

/-- The kernel `J` of a completed polynomial presentation. -/
abbrev ker : Ideal (polynomialCompletion A I ι) :=
  RingHom.ker P.toAlgHom

/-- The algebra extension associated with a completed polynomial presentation,
used to view `J / J²` as a `B`-module. -/
def toExtension : Algebra.Extension A B :=
  Algebra.Extension.ofSurjective P.toAlgHom P.surjective

/-- A completed polynomial presentation is a surjective `A`-algebra map from
`A[x_ι]^∧`. -/
theorem toAlgHom_surjective : Function.Surjective P.toAlgHom := P.surjective

/-- The kernel of `toExtension` recovers the kernel of the presentation map. -/
theorem toExtension_ker : P.toExtension.ker = P.ker := rfl

/-- The structure map of `ofQuotient J` is the canonical quotient map. -/
theorem ofQuotient_toAlgHom (J : Ideal (polynomialCompletion A I ι))
    (x : polynomialCompletion A I ι) :
    (ofQuotient J).toAlgHom x = Ideal.Quotient.mk J x := rfl

/-- The structure map of `ofSurjective f hf` is `f`. -/
theorem ofSurjective_toAlgHom (f : polynomialCompletion A I ι →ₐ[A] B)
    (hf : Function.Surjective f) :
    (ofSurjective f hf).toAlgHom = f := rfl

end Presentation

variable {A : Type u} [CommRing A] {ι : Type u}
variable {B : Type u} [CommRing B] [Algebra A B]

/-- The `n`-th stage of the extended `I`-adic filtration on `A[x_ι]`. -/
abbrev polynomialCompletionStage (I : Ideal A) (ι : Type u) (n : ℕ) :
    Submodule (MvPolynomial ι A) (MvPolynomial ι A) :=
  polynomialIdeal A I ι ^ n • ⊤

/-- Finite adic stages are the extended-ideal powers `I^n · A[x_ι]`. -/
theorem polynomialCompletionStage_def (I : Ideal A) (ι : Type u) (n : ℕ) :
    polynomialCompletionStage I ι n = polynomialIdeal A I ι ^ n • ⊤ := rfl

/-- Partial derivatives preserve each finite stage of the extended `I`-adic
filtration on `A[x_ι]`. -/
theorem pderiv_maps_pow_smul (I : Ideal A) (i : ι) (n : ℕ) :
    (polynomialCompletionStage I ι n).restrictScalars A ≤
      Submodule.comap (MvPolynomial.pderiv i).toLinearMap
        ((polynomialCompletionStage I ι n).restrictScalars A) := by
  simp only [polynomialCompletionStage, polynomialIdeal_eq_map, ← Ideal.map_pow,
    Submodule.restrictScalars_map_smul_eq, Submodule.restrictScalars_top]
  exact Submodule.smul_top_le_comap_smul_top (I ^ n) (MvPolynomial.pderiv i).toLinearMap

/-- The finite-stage map induced by `MvPolynomial.pderiv` on
`A[x_ι] / (I A[x_ι])^n`. -/
def pderivStage (I : Ideal A) (i : ι) (n : ℕ) :
    MvPolynomial ι A ⧸ polynomialCompletionStage I ι n →ₗ[A]
      MvPolynomial ι A ⧸ polynomialCompletionStage I ι n :=
  let p := polynomialCompletionStage I ι n
  (Submodule.Quotient.restrictScalarsEquiv A p).toLinearMap ∘ₗ
    Submodule.mapQ (p.restrictScalars A) (p.restrictScalars A)
      (MvPolynomial.pderiv i).toLinearMap (pderiv_maps_pow_smul I i n) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv A p).symm.toLinearMap

/-- Finite-stage partials send the class of a polynomial to the class of its
ordinary partial derivative. -/
theorem pderivStage_mk (I : Ideal A) (i : ι) (n : ℕ) (g : MvPolynomial ι A) :
    pderivStage I i n (Submodule.Quotient.mk g) =
      Submodule.Quotient.mk (MvPolynomial.pderiv i g) := rfl

/-- Finite-stage partials commute with adic transition maps. -/
theorem pderivStage_transition (I : Ideal A) (i : ι) {m n : ℕ} (hmn : m ≤ n)
    (x : polynomialCompletion A I ι) :
    AdicCompletion.transitionMap (polynomialIdeal A I ι) (MvPolynomial ι A) hmn
        (pderivStage I i n (x.val n)) =
      pderivStage I i m (x.val m) := by
  rw [← x.property hmn]
  induction x.val n using Quotient.inductionOn' with
  | h g => rfl

/-- The compatible family of finite-stage partial derivatives of an adic power series. -/
private def pderivValue (I : Ideal A) (i : ι) (x : polynomialCompletion A I ι) :
    polynomialCompletion A I ι :=
  ⟨fun n ↦ pderivStage I i n (x.val n), fun hmn ↦ pderivStage_transition I i hmn x⟩

/-- Stagewise completed partial differentiation preserves addition. -/
private theorem pderivValue_add (I : Ideal A) (i : ι)
    (x y : polynomialCompletion A I ι) :
    pderivValue I i (x + y) = pderivValue I i x + pderivValue I i y := by
  apply AdicCompletion.ext
  intro n
  exact map_add (pderivStage I i n) (x.val n) (y.val n)

/-- Stagewise completed partial differentiation commutes with scalars from `A`. -/
private theorem pderivValue_smul (I : Ideal A) (i : ι)
    (a : A) (x : polynomialCompletion A I ι) :
    pderivValue I i (a • x) = a • pderivValue I i x := by
  apply AdicCompletion.ext
  intro n
  exact map_smul (pderivStage I i n) a (x.val n)

/-- The partial derivative of an `I`-adic power series with respect to the
variable `i`, obtained by descending `MvPolynomial.pderiv` through each finite
adic stage. -/
@[no_expose] def pderiv (I : Ideal A) (i : ι) :
    polynomialCompletion A I ι →ₗ[A] polynomialCompletion A I ι where
  toFun := pderivValue I i
  map_add' := pderivValue_add I i
  map_smul' := pderivValue_smul I i

/-- Evaluating a completed partial at a finite stage recovers the stagewise
partial. -/
theorem eval_pderiv (I : Ideal A) (i : ι) (n : ℕ) (x : polynomialCompletion A I ι) :
    AdicCompletion.eval (polynomialIdeal A I ι) (MvPolynomial ι A) n (pderiv I i x) =
      pderivStage I i n
        (AdicCompletion.eval (polynomialIdeal A I ι) (MvPolynomial ι A) n x) := by
  simp only [pderiv, pderivValue, AdicCompletion.eval_apply, LinearMap.coe_mk, AddHom.coe_mk]

/-- Completed partials extend ordinary polynomial partials along the dense map
from `A[x_ι]`. -/
theorem pderiv_of (I : Ideal A) (i : ι) (g : MvPolynomial ι A) :
    pderiv I i (AdicCompletion.of (polynomialIdeal A I ι) (MvPolynomial ι A) g) =
      AdicCompletion.of (polynomialIdeal A I ι) (MvPolynomial ι A)
        (MvPolynomial.pderiv i g) := by
  apply AdicCompletion.ext
  intro n
  exact pderivStage_mk I i n g

private theorem pderiv_mul (I : Ideal A) (i : ι) (x y : polynomialCompletion A I ι) :
    pderiv I i (x * y) = pderiv I i x * y + x * pderiv I i y := by
  apply AdicCompletion.ext
  intro n
  change pderivStage I i n (x.val n * y.val n) =
    pderivStage I i n (x.val n) * y.val n + x.val n * pderivStage I i n (y.val n)
  induction x.val n, y.val n using Quotient.inductionOn₂' with
  | h f g =>
    change Submodule.Quotient.mk (MvPolynomial.pderiv i (f * g)) =
      Submodule.Quotient.mk (MvPolynomial.pderiv i f * g + f * MvPolynomial.pderiv i g)
    rw [MvPolynomial.pderiv_mul]

/-- The images in `B` of the completed partial derivatives of a kernel element. -/
private def jacobianOnKerValue (P : Presentation A B I ι) (g : P.ker) : ι → B :=
  fun i ↦ P.toAlgHom (pderiv I i (g : polynomialCompletion A I ι))

/-- The completed derivative images of kernel elements preserve addition. -/
private theorem jacobianOnKerValue_add (P : Presentation A B I ι) (g h : P.ker) :
    jacobianOnKerValue P (g + h) = jacobianOnKerValue P g + jacobianOnKerValue P h := by
  funext i
  change P.toAlgHom (pderiv I i ((g : polynomialCompletion A I ι) + h)) =
    P.toAlgHom (pderiv I i g) + P.toAlgHom (pderiv I i h)
  rw [map_add, map_add]

/-- The completed derivative images of kernel elements commute with scalars from `A`. -/
private theorem jacobianOnKerValue_smul (P : Presentation A B I ι) (a : A) (g : P.ker) :
    jacobianOnKerValue P (a • g) = a • jacobianOnKerValue P g := by
  funext i
  change P.toAlgHom (pderiv I i (a • (g : polynomialCompletion A I ι))) =
    a • P.toAlgHom (pderiv I i g)
  rw [map_smul, map_smul]

/-- The representative Jacobian on the kernel of a completed presentation,
sending `g ∈ J` to the images of the completed partials `∂g / ∂x_i`. -/
@[no_expose] def jacobianOnKer (P : Presentation A B I ι) :
    P.ker →ₗ[A] (ι → B) where
  toFun := jacobianOnKerValue P
  map_add' := jacobianOnKerValue_add P
  map_smul' := jacobianOnKerValue_smul P

/-- The representative Jacobian is given on kernel elements by completed
partials. -/
theorem jacobianOnKer_apply (P : Presentation A B I ι) (g : P.ker) (i : ι) :
    jacobianOnKer P g i = P.toAlgHom (pderiv I i (g : polynomialCompletion A I ι)) := by
  simp only [jacobianOnKer, jacobianOnKerValue, LinearMap.coe_mk, AddHom.coe_mk]

/-- The representative Jacobian vanishes on `J²`. -/
theorem jacobianOnKer_square (P : Presentation A B I ι) :
    ((P.ker • ⊤ : Submodule (polynomialCompletion A I ι) P.ker).restrictScalars A) ≤
      LinearMap.ker (jacobianOnKer P) := by
  intro x hx
  change x ∈ (P.ker • ⊤ : Submodule (polynomialCompletion A I ι) P.ker) at hx
  change jacobianOnKer P x = 0
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro g hg h _
    funext i
    change P.toAlgHom (pderiv I i (g * (h : polynomialCompletion A I ι))) = 0
    have hg' : P.toAlgHom g = 0 := hg
    have hh' : P.toAlgHom (h : polynomialCompletion A I ι) = 0 := h.property
    simp only [pderiv_mul, map_add, map_mul, hg', hh', mul_zero, zero_mul, add_zero]
  · intro x y hx hy
    rw [map_add, hx, hy, add_zero]

/-- The completed derivative images descended to the conormal quotient `J / J²`. -/
private def jacobianValue [Fintype ι] (P : Presentation A B I ι)
    (x : P.toExtension.Cotangent) : ι → B :=
  let p := (P.ker • ⊤ : Submodule (polynomialCompletion A I ι) P.ker)
  Submodule.liftQ (p.restrictScalars A) (jacobianOnKer P) (jacobianOnKer_square P)
    ((Submodule.Quotient.restrictScalarsEquiv A p).symm
      (Algebra.Extension.Cotangent.val x))

/-- The completed derivative map on the conormal quotient preserves addition. -/
private theorem jacobianValue_add [Fintype ι] (P : Presentation A B I ι)
    (x y : P.toExtension.Cotangent) :
    jacobianValue P (x + y) = jacobianValue P x + jacobianValue P y := by
  let p := (P.ker • ⊤ : Submodule (polynomialCompletion A I ι) P.ker)
  let f := (Submodule.liftQ (p.restrictScalars A) (jacobianOnKer P)
    (jacobianOnKer_square P)).comp
      (Submodule.Quotient.restrictScalarsEquiv A p).symm.toLinearMap
  exact map_add f (Algebra.Extension.Cotangent.val x) (Algebra.Extension.Cotangent.val y)

/-- The completed derivative map on the conormal quotient commutes with scalars from `B`. -/
private theorem jacobianValue_smul [Fintype ι] (P : Presentation A B I ι)
    (b : B) (x : P.toExtension.Cotangent) :
    jacobianValue P (b • x) = b • jacobianValue P x := by
  obtain ⟨g, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
  obtain ⟨r, rfl⟩ := P.surjective b
  have hsmul : P.toAlgHom r • Algebra.Extension.Cotangent.mk (P := P.toExtension) g =
      Algebra.Extension.Cotangent.mk (P := P.toExtension)
        ((show P.toExtension.Ring from r) • g) := by
    change (algebraMap P.toExtension.Ring B r) •
      Algebra.Extension.Cotangent.mk (P := P.toExtension) g = _
    rw [algebraMap_smul]
    exact (map_smul (Algebra.Extension.Cotangent.mk (P := P.toExtension))
      (show P.toExtension.Ring from r) g).symm
  rw [hsmul]
  funext i
  let g' : polynomialCompletion A I ι := g.val
  change P.toAlgHom (pderiv I i (r * g')) =
    P.toAlgHom r * P.toAlgHom (pderiv I i g')
  have hg : P.toAlgHom g' = 0 := g.property
  simp only [pderiv_mul, map_add, map_mul, hg, mul_zero, zero_add]

/-- The Jacobian of a completed presentation, obtained by descending the
representative map on `J` through `J / J²`. -/
@[no_expose] def jacobian [Fintype ι] (P : Presentation A B I ι) :
    P.toExtension.Cotangent →ₗ[B] (ι → B) where
  toFun := jacobianValue P
  map_add' := jacobianValue_add P
  map_smul' := jacobianValue_smul P

/-- The Jacobian sends the residue of `g ∈ J` to the images of the completed
partials `∂g / ∂x_i`. -/
theorem jacobian_apply [Fintype ι] (P : Presentation A B I ι)
    {g : polynomialCompletion A I ι} (hg : g ∈ P.ker) (i : ι) :
    jacobian P (Algebra.Extension.Cotangent.mk ⟨g, hg⟩) i =
      P.toAlgHom (pderiv I i g) := by
  change jacobianOnKer P ⟨g, hg⟩ i = _
  exact jacobianOnKer_apply P ⟨g, hg⟩ i

/-- The two-term completed naive cotangent complex of a presentation, with
degree-one term `J / J²`, degree-zero term `⊕ᵢ B dx_i`, and differential the
Jacobian of completed partials. Source degrees `-1` and `0` are encoded as
homological degrees `1` and `0` on `ChainComplex ℕ`. -/
def complex [Fintype ι] (P : Presentation A B I ι) :
    ChainComplex (ModuleCat B) ℕ :=
  ChainComplex.mk'
    (ModuleCat.of B (ι → B))
    (ModuleCat.of B P.toExtension.Cotangent)
    (ModuleCat.ofHom (jacobian P))
    (fun {_ _} _ ↦ ⟨ModuleCat.of B PUnit, 0, CategoryTheory.Limits.zero_comp⟩)

/-- The differential of the completed naive cotangent complex in degrees `1 → 0`
is the Jacobian. -/
theorem complex_d_one_zero [Fintype ι] (P : Presentation A B I ι) :
    (complex P).d 1 0 = ModuleCat.ofHom (jacobian P) :=
  ChainComplex.mk'_d_1_0 ..

/-- The degree-zero component is the free `B`-module on the variables. -/
def componentZeroIso [Fintype ι] (P : Presentation A B I ι) :
    (complex P).X 0 ≅ ModuleCat.of B (ι → B) :=
  Iso.refl _

/-- The degree-one component is the conormal module `J / J²`. -/
def componentOneIso [Fintype ι] (P : Presentation A B I ι) :
    (complex P).X 1 ≅ ModuleCat.of B P.toExtension.Cotangent :=
  Iso.refl _

/-- The completed naive cotangent complex attached to a completed-polynomial
presentation. -/
noncomputable abbrev naiveCotangent [Fintype ι] (I : Ideal A)
    (P : Presentation A B I ι) :
    ChainComplex (ModuleCat B) ℕ :=
  complex P

end Algebra.NaiveCotangent.Adic
