/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
public import Mathlib.Tactic.CrossRefAttribute
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
    polynomialIdeal A I ι = I.map (algebraMap A (MvPolynomial ι A)) := sorry

/-- The `I`-adic completion `A[x_ι]^∧` of a polynomial ring, taken along the
extended ideal `I · A[x_ι]`. -/
abbrev polynomialCompletion (A : Type u) [CommRing A] (I : Ideal A) (ι : Type u) : Type u :=
  AdicCompletion (polynomialIdeal A I ι) (MvPolynomial ι A)

/-- The completed polynomial ring is the adic completion of `A[x_ι]` along
`I · A[x_ι]`. -/
theorem polynomialCompletion_def (A : Type u) [CommRing A] (I : Ideal A) (ι : Type u) :
    polynomialCompletion A I ι =
      AdicCompletion (polynomialIdeal A I ι) (MvPolynomial ι A) := sorry

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
theorem toAlgHom_surjective : Function.Surjective P.toAlgHom := sorry

/-- The kernel of `toExtension` recovers the kernel of the presentation map. -/
theorem toExtension_ker : P.toExtension.ker = P.ker := sorry

/-- The structure map of `ofQuotient J` is the canonical quotient map. -/
theorem ofQuotient_toAlgHom (J : Ideal (polynomialCompletion A I ι))
    (x : polynomialCompletion A I ι) :
    (ofQuotient J).toAlgHom x = Ideal.Quotient.mk J x := sorry

/-- The structure map of `ofSurjective f hf` is `f`. -/
theorem ofSurjective_toAlgHom (f : polynomialCompletion A I ι →ₐ[A] B)
    (hf : Function.Surjective f) :
    (ofSurjective f hf).toAlgHom = f := sorry

end Presentation

variable {A : Type u} [CommRing A] {ι : Type u}
variable {B : Type u} [CommRing B] [Algebra A B]

/-- The `n`-th stage of the extended `I`-adic filtration on `A[x_ι]`. -/
abbrev polynomialCompletionStage (I : Ideal A) (ι : Type u) (n : ℕ) :
    Submodule (MvPolynomial ι A) (MvPolynomial ι A) :=
  polynomialIdeal A I ι ^ n • ⊤

/-- Finite adic stages are the extended-ideal powers `I^n · A[x_ι]`. -/
theorem polynomialCompletionStage_def (I : Ideal A) (ι : Type u) (n : ℕ) :
    polynomialCompletionStage I ι n = polynomialIdeal A I ι ^ n • ⊤ := sorry

/-- Partial derivatives preserve each finite stage of the extended `I`-adic
filtration on `A[x_ι]`. -/
theorem pderiv_maps_pow_smul (I : Ideal A) (i : ι) (n : ℕ) :
    (polynomialCompletionStage I ι n).restrictScalars A ≤
      Submodule.comap (MvPolynomial.pderiv i).toLinearMap
        ((polynomialCompletionStage I ι n).restrictScalars A) := sorry

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
      Submodule.Quotient.mk (MvPolynomial.pderiv i g) := sorry

/-- Finite-stage partials commute with adic transition maps. -/
theorem pderivStage_transition (I : Ideal A) (i : ι) {m n : ℕ} (hmn : m ≤ n)
    (x : polynomialCompletion A I ι) :
    AdicCompletion.transitionMap (polynomialIdeal A I ι) (MvPolynomial ι A) hmn
        (pderivStage I i n (x.val n)) =
      pderivStage I i m (x.val m) := sorry

/-- The partial derivative of an `I`-adic power series with respect to the
variable `i`, obtained by descending `MvPolynomial.pderiv` through each finite
adic stage. -/
def pderiv (I : Ideal A) (i : ι) :
    polynomialCompletion A I ι →ₗ[A] polynomialCompletion A I ι where
  toFun x := ⟨fun n ↦ pderivStage I i n (x.val n), fun hmn ↦ pderivStage_transition I i hmn x⟩
  map_add' := sorry
  map_smul' := sorry

/-- Evaluating a completed partial at a finite stage recovers the stagewise
partial. -/
theorem eval_pderiv (I : Ideal A) (i : ι) (n : ℕ) (x : polynomialCompletion A I ι) :
    AdicCompletion.eval (polynomialIdeal A I ι) (MvPolynomial ι A) n (pderiv I i x) =
      pderivStage I i n
        (AdicCompletion.eval (polynomialIdeal A I ι) (MvPolynomial ι A) n x) := sorry

/-- Completed partials extend ordinary polynomial partials along the dense map
from `A[x_ι]`. -/
theorem pderiv_of (I : Ideal A) (i : ι) (g : MvPolynomial ι A) :
    pderiv I i (AdicCompletion.of (polynomialIdeal A I ι) (MvPolynomial ι A) g) =
      AdicCompletion.of (polynomialIdeal A I ι) (MvPolynomial ι A)
        (MvPolynomial.pderiv i g) := sorry

/-- The representative Jacobian on the kernel of a completed presentation,
sending `g ∈ J` to the images of the completed partials `∂g / ∂x_i`. -/
def jacobianOnKer (P : Presentation A B I ι) :
    P.ker →ₗ[A] (ι → B) where
  toFun g i := P.toAlgHom (pderiv I i (g : polynomialCompletion A I ι))
  map_add' := sorry
  map_smul' := sorry

/-- The representative Jacobian is given on kernel elements by completed
partials. -/
theorem jacobianOnKer_apply (P : Presentation A B I ι) (g : P.ker) (i : ι) :
    jacobianOnKer P g i = P.toAlgHom (pderiv I i (g : polynomialCompletion A I ι)) := sorry

/-- The representative Jacobian vanishes on `J²`. -/
theorem jacobianOnKer_square (P : Presentation A B I ι) :
    ((P.ker • ⊤ : Submodule (polynomialCompletion A I ι) P.ker).restrictScalars A) ≤
      LinearMap.ker (jacobianOnKer P) := sorry

/-- The Jacobian of a completed presentation, obtained by descending the
representative map on `J` through `J / J²`. -/
def jacobian [Fintype ι] (P : Presentation A B I ι) :
    P.toExtension.Cotangent →ₗ[B] (ι → B) where
  toFun x :=
    let p := (P.ker • ⊤ : Submodule (polynomialCompletion A I ι) P.ker)
    Submodule.liftQ (p.restrictScalars A) (jacobianOnKer P) (jacobianOnKer_square P)
      ((Submodule.Quotient.restrictScalarsEquiv A p).symm
        (Algebra.Extension.Cotangent.val x))
  map_add' := sorry
  map_smul' := sorry

/-- The Jacobian sends the residue of `g ∈ J` to the images of the completed
partials `∂g / ∂x_i`. -/
theorem jacobian_apply [Fintype ι] (P : Presentation A B I ι)
    {g : polynomialCompletion A I ι} (hg : g ∈ P.ker) (i : ι) :
    jacobian P (Algebra.Extension.Cotangent.mk ⟨g, hg⟩) i =
      P.toAlgHom (pderiv I i g) := sorry

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
    (complex P).d 1 0 = ModuleCat.ofHom (jacobian P) := sorry

/-- The degree-zero component is the free `B`-module on the variables. -/
def componentZeroIso [Fintype ι] (P : Presentation A B I ι) :
    (complex P).X 0 ≅ ModuleCat.of B (ι → B) :=
  Iso.refl _

/-- The degree-one component is the conormal module `J / J²`. -/
def componentOneIso [Fintype ι] (P : Presentation A B I ι) :
    (complex P).X 1 ≅ ModuleCat.of B P.toExtension.Cotangent :=
  Iso.refl _

end Algebra.NaiveCotangent.Adic
