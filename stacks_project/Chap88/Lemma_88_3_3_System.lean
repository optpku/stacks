/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Data.PNat.Defs
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.Algebra.Homology.HomologicalComplex.ModIdeal.Change
public import ReasLib.Algebra.Homology.HomologicalComplex.ModIdeal.Tensor
public import ReasLib.Algebra.Homology.HomologicalComplex.Restriction
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import ReasLib.CategoryTheory.Pro.Sequential.Shift
public import ReasLib.RingTheory.Ideal.Quotient.Map
public import ReasLib.RingTheory.Ideal.Quotient.Pow
public import stacks_project.Chap88.«88_2_0_3_QuotientSystem»
public import stacks_project.Chap88.«88_3_0_1»

/-!
# Inverse systems of completed and stagewise naive cotangent complexes

This leaf owns the inverse systems `{NL_{B/A}^∧ ⊗_B B / I^{n+1} B}` and
`{NL_{B_{n+1}/A_{n+1}}}` in `Ch(B)` and `D(B)`, together with the canonical
comparison maps of complexes. Stage `n` uses the Section 88.2 rings `A_{n+1}`
and `B_{n+1}`.
-/

@[expose] public section

open CategoryTheory HomologicalComplex.ModIdeal MvPolynomial Opposite

noncomputable section

universe u

namespace Algebra.NaiveCotangent.Adic

variable {A B ι : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (I : Ideal A)
variable (P : Presentation A B I ι)

/-- The extended power `I^{n+1} B` used as the stage-`n` adic ideal. -/
abbrev stageIdeal (n : ℕ) : Ideal B :=
  (I ^ (n + 1)).map (algebraMap A B)

/-- Unfolding of the stage ideal as an extended power. -/
theorem stageIdeal_eq (n : ℕ) :
    stageIdeal I n = (I ^ (n + 1)).map (algebraMap A B) :=
  sorry

/-- Membership in the stage-`n` adic ideal is membership in `I^{n+1} B`. -/
theorem mem_stageIdeal (n : ℕ) {x : B} :
    x ∈ stageIdeal I n ↔ x ∈ (I ^ (n + 1)).map (algebraMap A B) :=
  sorry

/-- Successive stage ideals are nested as the exponent increases. -/
theorem stageIdeal_succ_le (n : ℕ) :
    (stageIdeal I (n + 1) : Ideal B) ≤ stageIdeal I n :=
  sorry

/-- The stage ring `A_{n+1} = A ⧸ I^{n+1}` from Section 88.2. -/
abbrev stageBase (n : ℕ) : Type u :=
  A ⧸ (I ^ (n + 1))

/-- Unfolding of the stage base ring. -/
theorem stageBase_eq (n : ℕ) :
    stageBase I n = (A ⧸ (I ^ (n + 1))) :=
  sorry

/-- The stage ring `B_{n+1} = B ⧸ I^{n+1} B` from Section 88.2. -/
abbrev stageRing (n : ℕ) : Type u :=
  B ⧸ stageIdeal I n

/-- The ℕ-indexed stage ring agrees with the Section 88.2 positive stage `B_{n+1}`. -/
theorem stageRing_succPNat (n : ℕ) :
    (B ⧸ stageIdeal I n) = (CommAlgCat.adicQuotientStage I B (Nat.succPNat n) : Type u) :=
  sorry

/-- The canonical algebra structure `A_{n+1} → B_{n+1}`. -/
instance stageAlgebra (n : ℕ) : Algebra (stageBase I n) ((B ⧸ stageIdeal I n)) :=
  Ideal.Quotient.mapAlgebra (algebraMap A B) (I ^ (n + 1))

/-- The scalar tower `A → A_{n+1} → B_{n+1}`. -/
instance stageIsScalarTower (n : ℕ) :
    IsScalarTower A (stageBase I n) ((B ⧸ stageIdeal I n)) :=
  sorry

/-- Images of the completed presentation variables in `B_{n+1}`. -/
def stageVal (n : ℕ) : ι → (B ⧸ stageIdeal I n) :=
  fun i ↦
    Ideal.Quotient.mk (stageIdeal I n)
      (P.toAlgHom
        (AdicCompletion.of (polynomialIdeal A I ι) (MvPolynomial ι A) (MvPolynomial.X i)))

/-- Evaluating a completed variable at stage `n` recovers `stageVal`. -/
theorem stageVal_eq (n : ℕ) (i : ι) :
    stageVal I P n i =
      Ideal.Quotient.mk (stageIdeal I n)
        (P.toAlgHom
          (AdicCompletion.of (polynomialIdeal A I ι) (MvPolynomial ι A) (MvPolynomial.X i))) :=
  sorry

/-- The induced polynomial presentation map `(A_{n+1})[x_ι] → B_{n+1}`. -/
def stageAlgHom (n : ℕ) :
    MvPolynomial ι (stageBase I n) →ₐ[stageBase I n] (B ⧸ stageIdeal I n) :=
  aeval (stageVal I P n)

/-- The stage presentation map evaluates variables to `stageVal`. -/
theorem stageAlgHom_X (n : ℕ) (i : ι) :
    stageAlgHom I P n (X i) = stageVal I P n i :=
  sorry

/-- The induced stage presentation map is surjective. -/
theorem stageAlgHom_surjective (n : ℕ) :
    Function.Surjective (stageAlgHom I P n) :=
  sorry

/-- The ordinary polynomial extension presenting `B_{n+1}` over `A_{n+1}`. -/
def stageExtension (n : ℕ) : Algebra.Extension (stageBase I n) ((B ⧸ stageIdeal I n)) :=
  Algebra.Extension.ofSurjective (stageAlgHom I P n) (stageAlgHom_surjective I P n)

/-- The kernel of the stage extension is the kernel of `stageAlgHom`. -/
theorem stageExtension_ker (n : ℕ) :
    (stageExtension I P n).ker = RingHom.ker (stageAlgHom I P n) :=
  sorry

/-- Polynomials in the extended power `(I · A[x_ι])^{n+1}` vanish after reducing
coefficients modulo `I^{n+1}`. -/
theorem toStagePolynomial_ker (n : ℕ) (g : MvPolynomial ι A)
    (hg : g ∈ polynomialIdeal A I ι ^ (n + 1)) :
    mapAlgHom (Ideal.Quotient.mkₐ A (I ^ (n + 1))) g = 0 :=
  sorry

/-- Evaluation of a completed polynomial in `A[x_ι]^∧` at the stage polynomial ring
`(A_{n+1})[x_ι]`. -/
def toStagePolynomial (n : ℕ) :
    polynomialCompletion A I ι →ₐ[A] MvPolynomial ι (stageBase I n) :=
  (Ideal.Quotient.liftₐ (polynomialIdeal A I ι ^ (n + 1))
      (mapAlgHom (Ideal.Quotient.mkₐ A (I ^ (n + 1))))
      (toStagePolynomial_ker (ι := ι) I n)).comp
    ((AdicCompletion.evalₐ (polynomialIdeal A I ι) (n + 1)).restrictScalars A)

/-- Completed polynomials in the presentation kernel remain in the stage kernel. -/
theorem toStagePolynomial_mem_ker (n : ℕ) {g : polynomialCompletion A I ι}
    (hg : g ∈ P.ker) :
    toStagePolynomial I n g ∈ (stageExtension I P n).ker :=
  sorry

/-- Representative Jacobian of a stage presentation, sending `g ∈ J_{n+1}` to the
images of ordinary partials `∂g / ∂x_i` in `B_{n+1}`. -/
def stageJacobianOnKer (n : ℕ) :
    (stageExtension I P n).ker →ₗ[stageBase I n] (ι → (B ⧸ stageIdeal I n)) where
  toFun g i := stageAlgHom I P n (MvPolynomial.pderiv i g.val)
  map_add' := sorry
  map_smul' := sorry

/-- The representative stage Jacobian vanishes on `J_{n+1}²`. -/
theorem stageJacobianOnKer_square (n : ℕ) :
    (((stageExtension I P n).ker • ⊤ :
        Submodule (stageExtension I P n).Ring (stageExtension I P n).ker).restrictScalars
      (stageBase I n)) ≤
      LinearMap.ker (stageJacobianOnKer I P n) :=
  sorry

/-- The Jacobian of a stage presentation, as a `B_{n+1}`-linear map on the conormal
module `J_{n+1} / J_{n+1}²`. -/
def stageJacobian (n : ℕ) :
    (stageExtension I P n).Cotangent →ₗ[(B ⧸ stageIdeal I n)] (ι → (B ⧸ stageIdeal I n)) where
  toFun x :=
    let p :=
      ((stageExtension I P n).ker • ⊤ :
        Submodule (stageExtension I P n).Ring (stageExtension I P n).ker)
    Submodule.liftQ (p.restrictScalars (stageBase I n)) (stageJacobianOnKer I P n)
      (stageJacobianOnKer_square I P n)
      ((Submodule.Quotient.restrictScalarsEquiv (stageBase I n) p).symm
        (Algebra.Extension.Cotangent.val x))
  map_add' := sorry
  map_smul' := sorry


/-- The two-term naive cotangent complex of the stage presentation
`B_{n+1} = A_{n+1}[x_ι] / J_{n+1}`, with degree-zero term `ι → B_{n+1}` and
degree-one term `J_{n+1} / J_{n+1}²`. -/
def stageComplex [Fintype ι] (n : ℕ) : ChainComplex (ModuleCat ((B ⧸ stageIdeal I n))) ℕ :=
  ChainComplex.mk'
    (ModuleCat.of ((B ⧸ stageIdeal I n)) (ι → (B ⧸ stageIdeal I n)))
    (ModuleCat.of ((B ⧸ stageIdeal I n)) (stageExtension I P n).Cotangent)
    (ModuleCat.ofHom (stageJacobian I P n))
    (fun {_ _} _ ↦
      ⟨ModuleCat.of ((B ⧸ stageIdeal I n)) PUnit, 0, CategoryTheory.Limits.zero_comp⟩)

/-- The differential of the stage complex in degrees `1 → 0` is the stage Jacobian. -/
theorem stageComplex_d_one_zero [Fintype ι] (n : ℕ) :
    (stageComplex I P n).d 1 0 = ModuleCat.ofHom (stageJacobian I P n) :=
  sorry

/-- The degree-zero component of the stage complex is the free module on the variables. -/
def stageComplex_componentZeroIso [Fintype ι] (n : ℕ) :
    (stageComplex I P n).X 0 ≅ ModuleCat.of ((B ⧸ stageIdeal I n)) (ι → (B ⧸ stageIdeal I n)) :=
  Iso.refl _

/-- The degree-one component of the stage complex is the stage conormal module. -/
def stageComplex_componentOneIso [Fintype ι] (n : ℕ) :
    (stageComplex I P n).X 1 ≅
      ModuleCat.of ((B ⧸ stageIdeal I n)) (stageExtension I P n).Cotangent :=
  Iso.refl _

/-- The stage complex regarded as a complex of `B`-modules by restriction of scalars
along `B → B_{n+1}`. -/
def stageComplexRestrict [Fintype ι] (n : ℕ) : ChainComplex (ModuleCat B) ℕ :=
  (stageComplex I P n).restrictScalarsAlong (Ideal.Quotient.mk (stageIdeal I n))

/-- Restriction of scalars along `B → B_{n+1}` recovers `stageComplexRestrict`. -/
theorem stageComplexRestrict_eq [Fintype ι] (n : ℕ) :
    stageComplexRestrict I P n =
      (stageComplex I P n).restrictScalarsAlong (Ideal.Quotient.mk (stageIdeal I n)) :=
  sorry

/-- The termwise quotient complex `NL_{B/A}^∧ / I^{n+1} NL_{B/A}^∧`, equivalently
`NL_{B/A}^∧ ⊗_B B / I^{n+1} B`. -/
def modComplex [Fintype ι] (n : ℕ) : ChainComplex (ModuleCat B) ℕ :=
  restrictedComplex (stageIdeal I n) (naiveCotangent I P)

/-- Unfolding of the mod-`I^{n+1}` completed naive cotangent complex. -/
theorem modComplex_eq [Fintype ι] (n : ℕ) :
    modComplex I P n = restrictedComplex (stageIdeal I n) (naiveCotangent I P) :=
  sorry

/-- Tensoring `NL_{B/A}^∧` by `B / I^{n+1} B` is canonically the termwise quotient
complex `modComplex`. -/
def modComplex_tensorIso [Fintype ι] (n : ℕ) :
    tensorQuotientComplex (stageIdeal I n) (naiveCotangent I P) ≅ modComplex I P n :=
  tensorQuotientIso (stageIdeal I n) (naiveCotangent I P)

/-- The inverse-system transition `NL_{B/A}^∧ / I^{n+2} → NL_{B/A}^∧ / I^{n+1}`. -/
def modSystemStep [Fintype ι] (n : ℕ) : modComplex I P (n + 1) ⟶ modComplex I P n :=
  restrictedOfLE (stageIdeal_succ_le I n) (naiveCotangent I P)

/-- The inverse system `{NL_{B/A}^∧ ⊗_B B / I^{n+1} B}` of complexes of `B`-modules. -/
def modSystem [Fintype ι] : SequentialInverseSystem (ChainComplex (ModuleCat B) ℕ) :=
  Functor.ofOpSequence (modSystemStep I P)

/-- Stages of `modSystem` are the termwise quotient complexes `modComplex`. -/
theorem modSystem_obj [Fintype ι] (n : ℕ) :
    (modSystem I P).obj (op n) = modComplex I P n :=
  sorry

/-- Successor maps of `modSystem` are the canonical change-of-ideal maps. -/
theorem modSystem_stepMap [Fintype ι] (n : ℕ) :
    SequentialInverseSystem.stepMap (modSystem I P) n = modSystemStep I P n :=
  sorry

/-- Coordinatewise reduction `(ι → B) → (ι → B_{n+1})`. -/
def modToStageZeroOnFree [Fintype ι] (n : ℕ) :
    (naiveCotangent I P).X 0 →ₗ[B] (stageComplexRestrict I P n).X 0 where
  toFun x i := Ideal.Quotient.mk (stageIdeal I n) (x i)
  map_add' := sorry
  map_smul' := sorry

/-- Coordinatewise reduction vanishes on representatives that are zero in
`NL_{B/A}^∧ / I^{n+1} NL_{B/A}^∧` in degree zero. -/
theorem modToStageZeroOnFree_eq_zero_of_projection [Fintype ι] (n : ℕ)
    {x : (naiveCotangent I P).X 0}
    (hx :
      HomologicalComplex.ModIdeal.projectionLinear (stageIdeal I n) (naiveCotangent I P) 0 x = 0) :
    modToStageZeroOnFree I P n x = 0 :=
  sorry

/-- Representative conormal map sending `g ∈ J` to the class of its stage polynomial
in `J_{n+1} / J_{n+1}²`. -/
def cotangentToStageOnKer (n : ℕ) :
    P.ker →ₗ[A] (stageExtension I P n).Cotangent where
  toFun g :=
    Algebra.Extension.Cotangent.mk (P := stageExtension I P n)
      ⟨toStagePolynomial I n (g : polynomialCompletion A I ι),
        toStagePolynomial_mem_ker I P n g.property⟩
  map_add' := sorry
  map_smul' := sorry

/-- The representative conormal map vanishes on `J²`. -/
theorem cotangentToStageOnKer_square (n : ℕ) :
    ((P.ker • ⊤ : Submodule (polynomialCompletion A I ι) P.ker).restrictScalars A) ≤
      LinearMap.ker (cotangentToStageOnKer I P n) :=
  sorry

/-- The induced map of conormal modules `J / J² → J_{n+1} / J_{n+1}²`. -/
def cotangentToStage (n : ℕ) :
    P.toExtension.Cotangent →ₗ[B] (stageExtension I P n).Cotangent where
  toFun x :=
    let p := (P.ker • ⊤ : Submodule (polynomialCompletion A I ι) P.ker)
    Submodule.liftQ (p.restrictScalars A) (cotangentToStageOnKer I P n)
      (cotangentToStageOnKer_square I P n)
      ((Submodule.Quotient.restrictScalarsEquiv A p).symm
        (Algebra.Extension.Cotangent.val x))
  map_add' := sorry
  map_smul' := sorry

/-- The conormal comparison vanishes on representatives that are zero in
`NL_{B/A}^∧ / I^{n+1} NL_{B/A}^∧` in degree one. -/
theorem cotangentToStage_eq_zero_of_projection [Fintype ι] (n : ℕ)
    {x : (naiveCotangent I P).X 1}
    (hx :
      HomologicalComplex.ModIdeal.projectionLinear (stageIdeal I n) (naiveCotangent I P) 1 x = 0) :
    cotangentToStage I P n x = 0 :=
  sorry

/-- Degree-zero comparison after reducing the free module on the variables
modulo `I^{n+1}`. -/
def modToStageZeroLinear [Fintype ι] (n : ℕ) :
    (modComplex I P n).X 0 →ₗ[B] (stageComplexRestrict I P n).X 0 where
  toFun x := Quotient.liftOn x (modToStageZeroOnFree I P n) sorry
  map_add' := sorry
  map_smul' := sorry

/-- Degree-one comparison after reducing the conormal module modulo `I^{n+1}`. -/
def modToStageOneLinear [Fintype ι] (n : ℕ) :
    (modComplex I P n).X 1 →ₗ[B] (stageComplexRestrict I P n).X 1 where
  toFun x := Quotient.liftOn x (cotangentToStage I P n) sorry
  map_add' := sorry
  map_smul' := sorry

/-- Degree-zero component of the canonical comparison of complexes. -/
def modToStage_f_zero [Fintype ι] (n : ℕ) :
    (modComplex I P n).X 0 ⟶ (stageComplexRestrict I P n).X 0 :=
  ModuleCat.ofHom (modToStageZeroLinear I P n)

/-- Degree-one component of the canonical comparison of complexes. -/
def modToStage_f_one [Fintype ι] (n : ℕ) :
    (modComplex I P n).X 1 ⟶ (stageComplexRestrict I P n).X 1 :=
  ModuleCat.ofHom (modToStageOneLinear I P n)

/-- The degree `1 → 0` square of the canonical comparison commutes. -/
theorem modToStage_one_zero_comm [Fintype ι] (n : ℕ) :
    modToStage_f_one I P n ≫ (stageComplexRestrict I P n).d 1 0 =
      (modComplex I P n).d 1 0 ≫ modToStage_f_zero I P n :=
  sorry

/-- Higher components of the canonical comparison form commutative squares. -/
theorem modToStage_succ_comm [Fintype ι] (n k : ℕ)
    (p :
      Σ' (zero : (modComplex I P n).X k ⟶ (stageComplexRestrict I P n).X k)
        (one : (modComplex I P n).X (k + 1) ⟶ (stageComplexRestrict I P n).X (k + 1)),
        one ≫ (stageComplexRestrict I P n).d (k + 1) k =
          (modComplex I P n).d (k + 1) k ≫ zero) :
    (0 : (modComplex I P n).X (k + 2) ⟶ (stageComplexRestrict I P n).X (k + 2)) ≫
        (stageComplexRestrict I P n).d (k + 2) (k + 1) =
      (modComplex I P n).d (k + 2) (k + 1) ≫ p.2.1 :=
  sorry

/-- The canonical chain map
`NL_{B/A}^∧ ⊗_B B / I^{n+1} B ⟶ NL_{B_{n+1}/A_{n+1}}` of complexes of
`B`-modules. -/
def modToStage [Fintype ι] (n : ℕ) : modComplex I P n ⟶ stageComplexRestrict I P n :=
  ChainComplex.mkHom _ _ (modToStage_f_zero I P n) (modToStage_f_one I P n)
    (modToStage_one_zero_comm I P n)
    (fun k p ↦ ⟨0, modToStage_succ_comm I P n k p⟩)

/-- The degree-zero component of `modToStage` is the free-module comparison. -/
theorem modToStage_f_zero_eq [Fintype ι] (n : ℕ) :
    (modToStage I P n).f 0 = modToStage_f_zero I P n :=
  sorry

/-- The degree-one component of `modToStage` is the conormal comparison. -/
theorem modToStage_f_one_eq [Fintype ι] (n : ℕ) :
    (modToStage I P n).f 1 = modToStage_f_one I P n :=
  sorry

/-- Coordinatewise transition `(ι → B_{n+2}) → (ι → B_{n+1})`. -/
def stageStepZeroOnFree (n : ℕ) :
    (ι → (B ⧸ stageIdeal I (n + 1))) →ₗ[B] (ι → (B ⧸ stageIdeal I n)) where
  toFun x i := Submodule.factor (stageIdeal_succ_le I n) (x i)
  map_add' := sorry
  map_smul' := sorry

/-- Coefficientwise polynomial transition `(A_{n+2})[x_ι] → (A_{n+1})[x_ι]`. -/
def stagePolyMap (n : ℕ) :
    MvPolynomial ι (stageBase I (n + 1)) →+* MvPolynomial ι (stageBase I n) :=
  MvPolynomial.map (algebraMap (stageBase I (n + 1)) (stageBase I n))

/-- The polynomial transition sends the stage kernel at `n+1` into the stage kernel at `n`. -/
theorem stagePolyMap_mem_ker (n : ℕ) {g : MvPolynomial ι (stageBase I (n + 1))}
    (hg : g ∈ (stageExtension I P (n + 1)).ker) :
    stagePolyMap I n g ∈ (stageExtension I P n).ker :=
  sorry

/-- Representative transition of stage kernels. -/
def stageStepOneOnKer (n : ℕ) :
    (stageExtension I P (n + 1)).ker →ₗ[A] (stageExtension I P n).Cotangent where
  toFun g :=
    Algebra.Extension.Cotangent.mk ⟨stagePolyMap I n g.val, stagePolyMap_mem_ker I P n g.property⟩
  map_add' := sorry
  map_smul' := sorry

/-- The representative stage-kernel transition vanishes on squares. -/
theorem stageStepOneOnKer_square (n : ℕ) :
    (((stageExtension I P (n + 1)).ker • ⊤ :
          Submodule (stageExtension I P (n + 1)).Ring
            (stageExtension I P (n + 1)).ker).restrictScalars A) ≤
      LinearMap.ker (stageStepOneOnKer I P n) :=
  sorry

/-- The induced transition of stage conormal modules. -/
def stageStepOneLinear (n : ℕ) :
    (stageExtension I P (n + 1)).Cotangent →ₗ[B] (stageExtension I P n).Cotangent where
  toFun x :=
    let p :=
      ((stageExtension I P (n + 1)).ker • ⊤ :
        Submodule (stageExtension I P (n + 1)).Ring (stageExtension I P (n + 1)).ker)
    Submodule.liftQ (p.restrictScalars A) (stageStepOneOnKer I P n)
      (stageStepOneOnKer_square I P n)
      ((Submodule.Quotient.restrictScalarsEquiv A p).symm
        (Algebra.Extension.Cotangent.val x))
  map_add' := sorry
  map_smul' := sorry

/-- Degree-zero component of the stage transition of restricted complexes. -/
def stageStep_f_zero [Fintype ι] (n : ℕ) :
    (stageComplexRestrict I P (n + 1)).X 0 ⟶ (stageComplexRestrict I P n).X 0 :=
  ModuleCat.ofHom (stageStepZeroOnFree I n)

/-- Degree-one component of the stage transition of restricted complexes. -/
def stageStep_f_one [Fintype ι] (n : ℕ) :
    (stageComplexRestrict I P (n + 1)).X 1 ⟶ (stageComplexRestrict I P n).X 1 :=
  ModuleCat.ofHom (stageStepOneLinear I P n)

/-- The degree `1 → 0` square of the stage transition commutes. -/
theorem stageStep_one_zero_comm [Fintype ι] (n : ℕ) :
    stageStep_f_one I P n ≫ (stageComplexRestrict I P n).d 1 0 =
      (stageComplexRestrict I P (n + 1)).d 1 0 ≫ stageStep_f_zero I P n :=
  sorry

/-- Higher components of the stage transition form commutative squares. -/
theorem stageStep_succ_comm [Fintype ι] (n k : ℕ)
    (p :
      Σ' (zero :
          (stageComplexRestrict I P (n + 1)).X k ⟶ (stageComplexRestrict I P n).X k)
        (one :
          (stageComplexRestrict I P (n + 1)).X (k + 1) ⟶
            (stageComplexRestrict I P n).X (k + 1)),
        one ≫ (stageComplexRestrict I P n).d (k + 1) k =
          (stageComplexRestrict I P (n + 1)).d (k + 1) k ≫ zero) :
    (0 :
          (stageComplexRestrict I P (n + 1)).X (k + 2) ⟶
            (stageComplexRestrict I P n).X (k + 2)) ≫
        (stageComplexRestrict I P n).d (k + 2) (k + 1) =
      (stageComplexRestrict I P (n + 1)).d (k + 2) (k + 1) ≫ p.2.1 :=
  sorry

/-- The transition map of stage complexes of `B`-modules. -/
def stageSystemStep [Fintype ι] (n : ℕ) :
    stageComplexRestrict I P (n + 1) ⟶ stageComplexRestrict I P n :=
  ChainComplex.mkHom _ _ (stageStep_f_zero I P n) (stageStep_f_one I P n)
    (stageStep_one_zero_comm I P n)
    (fun k p ↦ ⟨0, stageStep_succ_comm I P n k p⟩)

/-- The inverse system `{NL_{B_{n+1}/A_{n+1}}}` of complexes of `B`-modules. -/
def stageSystem [Fintype ι] : SequentialInverseSystem (ChainComplex (ModuleCat B) ℕ) :=
  Functor.ofOpSequence (stageSystemStep I P)

/-- Stages of `stageSystem` are the restricted stage complexes. -/
theorem stageSystem_obj [Fintype ι] (n : ℕ) :
    (stageSystem I P).obj (op n) = stageComplexRestrict I P n :=
  sorry

/-- Successor maps of `stageSystem` are the restricted stage transitions. -/
theorem stageSystem_stepMap [Fintype ι] (n : ℕ) :
    SequentialInverseSystem.stepMap (stageSystem I P) n = stageSystemStep I P n :=
  sorry

/-- Naturality of the canonical comparison with respect to successor transitions. -/
theorem modToStage_naturality [Fintype ι] (n : ℕ) :
    (modSystem I P).map (homOfLE (Nat.le_add_right n 1)).op ≫ modToStage I P n =
      modToStage I P (n + 1) ≫
        (stageSystem I P).map (homOfLE (Nat.le_add_right n 1)).op :=
  sorry

/-- The canonical comparison as a morphism of inverse systems of complexes. -/
def modToStageNatTrans [Fintype ι] : modSystem I P ⟶ stageSystem I P :=
  NatTrans.ofOpSequence (modToStage I P) (modToStage_naturality I P)

/-- Components of `modToStageNatTrans` are the chain maps `modToStage`. -/
theorem modToStageNatTrans_app [Fintype ι] (n : ℕ) :
    (modToStageNatTrans I P).app (op n) = modToStage I P n :=
  sorry

/-- The derived inverse system `{NL_{B/A}^∧ ⊗_B B / I^{n+1} B}` in `D(B)`. -/
def modDerivedSystem [Fintype ι] : SequentialInverseSystem (DerivedCategory (ModuleCat B)) :=
  modSystem I P ⋙
    ComplexShape.embeddingDownNat.extendFunctor (ModuleCat B) ⋙ DerivedCategory.Q

/-- Stages of `modDerivedSystem` are the derived images of `modComplex`. -/
theorem modDerivedSystem_obj [Fintype ι] (n : ℕ) :
    (modDerivedSystem I P).obj (op n) =
      DerivedCategory.Q.obj ((modComplex I P n).extend ComplexShape.embeddingDownNat) :=
  sorry

/-- The derived inverse system `{NL_{B_{n+1}/A_{n+1}}}` in `D(B)`. -/
def stageDerivedSystem [Fintype ι] : SequentialInverseSystem (DerivedCategory (ModuleCat B)) :=
  stageSystem I P ⋙
    ComplexShape.embeddingDownNat.extendFunctor (ModuleCat B) ⋙ DerivedCategory.Q

/-- Stages of `stageDerivedSystem` are the derived images of the restricted stage
complexes. -/
theorem stageDerivedSystem_obj [Fintype ι] (n : ℕ) :
    (stageDerivedSystem I P).obj (op n) =
      DerivedCategory.Q.obj
        ((stageComplexRestrict I P n).extend ComplexShape.embeddingDownNat) :=
  sorry

/-- The canonical comparison, whiskered to a morphism of inverse systems in `D(B)`. -/
def modToStageDerivedNatTrans [Fintype ι] : modDerivedSystem I P ⟶ stageDerivedSystem I P :=
  Functor.whiskerRight
    (Functor.whiskerRight (modToStageNatTrans I P)
      (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat B)))
    DerivedCategory.Q

/-- The sequential pro-morphism in `D(B)` represented by the derived comparison. -/
def modToStageDerivedHom [Fintype ι] :
    Pro.SequentialHom (modDerivedSystem I P) (stageDerivedSystem I P) :=
  Pro.SequentialHom.ofNatTrans (modToStageDerivedNatTrans I P)

/-- The derived comparison representative uses the identity reindexing. -/
theorem modToStageDerivedHom_reindex [Fintype ι] :
    (modToStageDerivedHom I P).reindex = OrderHom.id :=
  sorry

end Algebra.NaiveCotangent.Adic
