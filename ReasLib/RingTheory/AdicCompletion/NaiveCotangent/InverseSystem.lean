module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.Algebra.Homology.HomologicalComplex.ModIdeal.Change
public import ReasLib.Algebra.Homology.HomologicalComplex.ModIdeal.Tensor
public import ReasLib.Algebra.Homology.HomologicalComplex.Restriction
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import ReasLib.CategoryTheory.Pro.Sequential.Shift
public import ReasLib.RingTheory.Ideal.Quotient.Map
public import ReasLib.RingTheory.Ideal.Quotient.Pow
public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent

/-!
# Inverse systems of completed and stagewise naive cotangent complexes

The ordinary reductions of a completed Jacobian complex and the Jacobian
complexes of the quotient presentations form inverse systems. Their canonical
comparison is induced by coefficient and relation reduction.
-/

@[expose] public section

open CategoryTheory HomologicalComplex.ModIdeal MvPolynomial Opposite
open scoped ChangeOfRings

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

/-- The positive adic quotient ring `A ⧸ I^{n+1}`. -/
abbrev stageBase (n : ℕ) : Type u :=
  A ⧸ (I ^ (n + 1))

/-- Unfolding of the stage base ring. -/
theorem stageBase_eq (n : ℕ) :
    stageBase I n = (A ⧸ (I ^ (n + 1))) :=
  sorry

/-- The positive adic quotient ring `B ⧸ I^{n+1} B`. -/
abbrev stageRing (n : ℕ) : Type u :=
  B ⧸ stageIdeal I n

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

/-- Over a Noetherian base, reduction of a completed presentation is surjective. -/
theorem stageAlgHom_surjective [IsNoetherianRing A] (n : ℕ) :
    Function.Surjective (stageAlgHom I P n) :=
  sorry

/-- The kernel of polynomial evaluation at an adic stage. -/
abbrev stageKernel (n : ℕ) : Ideal (MvPolynomial ι (stageBase I n)) :=
  RingHom.ker (stageAlgHom I P n)

/-- The conormal module of stage evaluation, extended to the target quotient ring. -/
def stageConormal (n : ℕ) : ModuleCat (B ⧸ stageIdeal I n) :=
  (ModuleCat.extendScalars (stageAlgHom I P n).toRingHom).obj
    (ModuleCat.of _ (stageKernel I P n).Cotangent)

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
theorem toStagePolynomial_mem_ker [IsNoetherianRing A] (n : ℕ) {g : polynomialCompletion A I ι}
    (hg : g ∈ P.ker) :
    toStagePolynomial I n g ∈ stageKernel I P n :=
  sorry

private def stageJacobianOnKerValue (n : ℕ) (g : stageKernel I P n) :
    (ModuleCat.restrictScalars (stageAlgHom I P n).toRingHom).obj
      (ModuleCat.of _ (ι → (B ⧸ stageIdeal I n))) :=
  fun i ↦ stageAlgHom I P n (MvPolynomial.pderiv i g.val)

/-- Ordinary partial derivatives on the evaluation kernel preserve addition. -/
private theorem stageJacobianOnKer_add (n : ℕ) (g h : stageKernel I P n) :
    stageJacobianOnKerValue I P n (g + h) =
      stageJacobianOnKerValue I P n g + stageJacobianOnKerValue I P n h := sorry

/-- The kernel Jacobian is linear for polynomial scalars acting by evaluation. -/
private theorem stageJacobianOnKer_smul (n : ℕ)
    (r : MvPolynomial ι (stageBase I n)) (g : stageKernel I P n) :
    stageJacobianOnKerValue I P n (r • g) = r • stageJacobianOnKerValue I P n g := sorry

/-- The ordinary Jacobian on the evaluation kernel, with polynomial scalar action. -/
@[no_expose] def stageJacobianOnKer (n : ℕ) :
    stageKernel I P n →ₗ[MvPolynomial ι (stageBase I n)]
      (ModuleCat.restrictScalars (stageAlgHom I P n).toRingHom).obj
        (ModuleCat.of _ (ι → (B ⧸ stageIdeal I n))) where
  toFun := stageJacobianOnKerValue I P n
  map_add' := stageJacobianOnKer_add I P n
  map_smul' := stageJacobianOnKer_smul I P n

/-- The ordinary Jacobian vanishes on the square of the evaluation kernel. -/
theorem stageJacobianOnKer_square (n : ℕ) :
    (stageKernel I P n • ⊤ :
      Submodule (MvPolynomial ι (stageBase I n)) (stageKernel I P n)) ≤
        LinearMap.ker (stageJacobianOnKer I P n) := sorry

private def stageJacobianValue (n : ℕ) :
    stageConormal I P n →ₗ[B ⧸ stageIdeal I n] (ι → (B ⧸ stageIdeal I n)) :=
  (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (stageAlgHom I P n).toRingHom
    (X := ModuleCat.of _ (stageKernel I P n).Cotangent)
    (Y := ModuleCat.of _ (ι → (B ⧸ stageIdeal I n)))
    (ModuleCat.ofHom (Y := (ModuleCat.restrictScalars (stageAlgHom I P n).toRingHom).obj
        (ModuleCat.of _ (ι → (B ⧸ stageIdeal I n))))
      (Submodule.liftQ _ (stageJacobianOnKer I P n)
        (stageJacobianOnKer_square I P n)))).hom

/-- The scalar-extended conormal Jacobian preserves addition. -/
private theorem stageJacobian_add (n : ℕ) (x y : stageConormal I P n) :
    stageJacobianValue I P n (x + y) =
      stageJacobianValue I P n x + stageJacobianValue I P n y := sorry

/-- The scalar-extended conormal Jacobian is linear over the quotient ring. -/
private theorem stageJacobian_smul (n : ℕ) (r : B ⧸ stageIdeal I n)
    (x : stageConormal I P n) :
    stageJacobianValue I P n (r • x) = r • stageJacobianValue I P n x := sorry

/-- The quotient-ring-linear Jacobian on the scalar-extended conormal module. -/
@[no_expose] def stageJacobian (n : ℕ) :
    stageConormal I P n →ₗ[B ⧸ stageIdeal I n] (ι → (B ⧸ stageIdeal I n)) where
  toFun := stageJacobianValue I P n
  map_add' := stageJacobian_add I P n
  map_smul' := stageJacobian_smul I P n

/-- The two-term polynomial Jacobian complex of stage evaluation, with free
degree-zero term and scalar-extended conormal module in degree one. -/
def stageComplex [Fintype ι] (n : ℕ) : ChainComplex (ModuleCat ((B ⧸ stageIdeal I n))) ℕ :=
  ChainComplex.mk'
    (ModuleCat.of ((B ⧸ stageIdeal I n)) (ι → (B ⧸ stageIdeal I n)))
    (stageConormal I P n)
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
      stageConormal I P n :=
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
private def modToStageZeroOnFreeValue [Fintype ι] (n : ℕ) :
    (naiveCotangent I P).X 0 → (stageComplexRestrict I P n).X 0 :=
  fun x i ↦ Ideal.Quotient.mk (stageIdeal I n) (x i)

/-- Coordinatewise quotient reduction preserves addition. -/
private theorem modToStageZeroOnFree_add [Fintype ι] (n : ℕ) (x y : (naiveCotangent I P).X 0) :
    modToStageZeroOnFreeValue I P n (x + y) =
      modToStageZeroOnFreeValue I P n x + modToStageZeroOnFreeValue I P n y := sorry

/-- Coordinatewise quotient reduction commutes with scalars. -/
private theorem modToStageZeroOnFree_smul [Fintype ι] (n : ℕ) (r : B) (x : (naiveCotangent I P).X 0) :
    modToStageZeroOnFreeValue I P n (r • x) = r • modToStageZeroOnFreeValue I P n x := sorry

/-- Coordinatewise quotient reduction as a linear map. -/
@[no_expose] def modToStageZeroOnFree [Fintype ι] (n : ℕ) :
    (naiveCotangent I P).X 0 →ₗ[B] (stageComplexRestrict I P n).X 0 where
  toFun := modToStageZeroOnFreeValue I P n
  map_add' := modToStageZeroOnFree_add I P n
  map_smul' := modToStageZeroOnFree_smul I P n

/-- Coordinatewise reduction vanishes on representatives that are zero in
`NL_{B/A}^∧ / I^{n+1} NL_{B/A}^∧` in degree zero. -/
theorem modToStageZeroOnFree_eq_zero_of_projection [Fintype ι] (n : ℕ)
    {x : (naiveCotangent I P).X 0}
    (hx :
      HomologicalComplex.ModIdeal.projectionLinear (stageIdeal I n) (naiveCotangent I P) 0 x = 0) :
    modToStageZeroOnFree I P n x = 0 :=
  sorry

private def cotangentToStageOnKerValue [IsNoetherianRing A] (n : ℕ)
    (g : P.ker) :
    (ModuleCat.restrictScalars (algebraMap A B)).obj
      ((ModuleCat.restrictScalars (algebraMap B (B ⧸ stageIdeal I n))).obj
        (stageConormal I P n)) :=
  (1 : B ⧸ stageIdeal I n) ⊗ₜ[MvPolynomial ι (stageBase I n), (stageAlgHom I P n).toRingHom]
    ((stageKernel I P n).toCotangent
      ⟨toStagePolynomial I n g.val, toStagePolynomial_mem_ker I P n g.property⟩)

/-- Reduction of completed relations to tensor-conormal classes preserves addition. -/
private theorem cotangentToStageOnKer_add [IsNoetherianRing A] (n : ℕ) (g h : P.ker) :
    cotangentToStageOnKerValue I P n (g + h) =
      cotangentToStageOnKerValue I P n g + cotangentToStageOnKerValue I P n h := sorry

/-- Reduction of completed relations to tensor-conormal classes is `A`-linear. -/
private theorem cotangentToStageOnKer_smul [IsNoetherianRing A] (n : ℕ) (r : A) (g : P.ker) :
    cotangentToStageOnKerValue I P n (r • g) = r • cotangentToStageOnKerValue I P n g := sorry

/-- A completed relation maps to one tensor the conormal class of its reduction. -/
@[no_expose] def cotangentToStageOnKer [IsNoetherianRing A] (n : ℕ) :
    P.ker →ₗ[A] (ModuleCat.restrictScalars (algebraMap A B)).obj
      ((ModuleCat.restrictScalars (algebraMap B (B ⧸ stageIdeal I n))).obj
        (stageConormal I P n)) where
  toFun := cotangentToStageOnKerValue I P n
  map_add' := cotangentToStageOnKer_add I P n
  map_smul' := cotangentToStageOnKer_smul I P n

/-- Reduction of relations annihilates the square of the completed kernel. -/
theorem cotangentToStageOnKer_square [IsNoetherianRing A] (n : ℕ) :
    ((P.ker • ⊤ : Submodule (polynomialCompletion A I ι) P.ker).restrictScalars A) ≤
      LinearMap.ker (cotangentToStageOnKer I P n) := sorry

private def cotangentToStageValue [IsNoetherianRing A] (n : ℕ)
    (x : P.toExtension.Cotangent) :
    (ModuleCat.restrictScalars (algebraMap B (B ⧸ stageIdeal I n))).obj
      (stageConormal I P n) :=
  let p := (P.ker • ⊤ : Submodule (polynomialCompletion A I ι) P.ker)
  Submodule.liftQ (p.restrictScalars A) (cotangentToStageOnKer I P n)
    (cotangentToStageOnKer_square I P n)
    ((Submodule.Quotient.restrictScalarsEquiv A p).symm
      (Algebra.Extension.Cotangent.val x))

/-- The descended conormal comparison preserves addition. -/
private theorem cotangentToStage_add [IsNoetherianRing A] (n : ℕ) (x y : P.toExtension.Cotangent) :
    cotangentToStageValue I P n (x + y) =
      cotangentToStageValue I P n x + cotangentToStageValue I P n y := sorry

/-- The descended conormal comparison is `B`-linear. -/
private theorem cotangentToStage_smul [IsNoetherianRing A] (n : ℕ) (r : B)
    (x : P.toExtension.Cotangent) :
    cotangentToStageValue I P n (r • x) = r • cotangentToStageValue I P n x := sorry

/-- The canonical map from completed conormals to stage tensor-conormals. -/
@[no_expose] def cotangentToStage [IsNoetherianRing A] (n : ℕ) :
    P.toExtension.Cotangent →ₗ[B]
      (ModuleCat.restrictScalars (algebraMap B (B ⧸ stageIdeal I n))).obj
        (stageConormal I P n) where
  toFun := cotangentToStageValue I P n
  map_add' := cotangentToStage_add I P n
  map_smul' := cotangentToStage_smul I P n

/-- The conormal comparison vanishes on representatives that are zero in
`NL_{B/A}^∧ / I^{n+1} NL_{B/A}^∧` in degree one. -/
theorem cotangentToStage_eq_zero_of_projection [IsNoetherianRing A] [Fintype ι] (n : ℕ)
    {x : (naiveCotangent I P).X 1}
    (hx :
      HomologicalComplex.ModIdeal.projectionLinear (stageIdeal I n) (naiveCotangent I P) 1 x = 0) :
    cotangentToStage I P n x = 0 :=
  sorry

/-- Degree-zero comparison after reducing the free module on the variables
modulo `I^{n+1}`. -/
theorem modToStageZeroLinear_wellDefined [Fintype ι] (n : ℕ)
    (x y : (naiveCotangent I P).X 0)
    (h : (HomologicalComplex.ModIdeal.projectionLinear (stageIdeal I n)
      (naiveCotangent I P) 0) x =
      (HomologicalComplex.ModIdeal.projectionLinear (stageIdeal I n)
        (naiveCotangent I P) 0) y) :
    modToStageZeroOnFree I P n x = modToStageZeroOnFree I P n y := sorry

private def modToStageZeroLinearValue [Fintype ι] (n : ℕ)
    (x : (modComplex I P n).X 0) : (stageComplexRestrict I P n).X 0 :=
  Quotient.liftOn x (modToStageZeroOnFree I P n) (fun x y h ↦
    modToStageZeroLinear_wellDefined I P n x y (Quotient.sound h))

/-- The quotient comparison preserves addition. -/
private theorem modToStageZeroLinear_add [Fintype ι] (n : ℕ) (x y : (modComplex I P n).X 0) :
    modToStageZeroLinearValue I P n (x + y) =
      modToStageZeroLinearValue I P n x + modToStageZeroLinearValue I P n y := sorry

/-- The quotient comparison is linear over the original algebra. -/
private theorem modToStageZeroLinear_smul [Fintype ι] (n : ℕ) (r : B) (x : (modComplex I P n).X 0) :
    modToStageZeroLinearValue I P n (r • x) = r • modToStageZeroLinearValue I P n x := sorry

/-- The descended comparison in degree 0. -/
@[no_expose] def modToStageZeroLinear [Fintype ι] (n : ℕ) :
    (modComplex I P n).X 0 →ₗ[B] (stageComplexRestrict I P n).X 0 where
  toFun := modToStageZeroLinearValue I P n
  map_add' := modToStageZeroLinear_add I P n
  map_smul' := modToStageZeroLinear_smul I P n

/-- Degree-one comparison after reducing the conormal module modulo `I^{n+1}`. -/
theorem modToStageOneLinear_wellDefined [IsNoetherianRing A] [Fintype ι] (n : ℕ)
    (x y : (naiveCotangent I P).X 1)
    (h : (HomologicalComplex.ModIdeal.projectionLinear (stageIdeal I n)
      (naiveCotangent I P) 1) x =
      (HomologicalComplex.ModIdeal.projectionLinear (stageIdeal I n)
        (naiveCotangent I P) 1) y) :
    cotangentToStage I P n x = cotangentToStage I P n y := sorry

private def modToStageOneLinearValue [IsNoetherianRing A] [Fintype ι] (n : ℕ)
    (x : (modComplex I P n).X 1) : (stageComplexRestrict I P n).X 1 :=
  Quotient.liftOn x (cotangentToStage I P n) (fun x y h ↦
    modToStageOneLinear_wellDefined I P n x y (Quotient.sound h))

/-- The quotient comparison preserves addition. -/
private theorem modToStageOneLinear_add [IsNoetherianRing A] [Fintype ι]
    (n : ℕ) (x y : (modComplex I P n).X 1) :
    modToStageOneLinearValue I P n (x + y) =
      modToStageOneLinearValue I P n x + modToStageOneLinearValue I P n y := sorry

/-- The quotient comparison is linear over the original algebra. -/
private theorem modToStageOneLinear_smul [IsNoetherianRing A] [Fintype ι]
    (n : ℕ) (r : B) (x : (modComplex I P n).X 1) :
    modToStageOneLinearValue I P n (r • x) = r • modToStageOneLinearValue I P n x := sorry

/-- The descended comparison in degree 1. -/
@[no_expose] def modToStageOneLinear [IsNoetherianRing A] [Fintype ι] (n : ℕ) :
    (modComplex I P n).X 1 →ₗ[B] (stageComplexRestrict I P n).X 1 where
  toFun := modToStageOneLinearValue I P n
  map_add' := modToStageOneLinear_add I P n
  map_smul' := modToStageOneLinear_smul I P n

/-- Degree-zero component of the canonical comparison of complexes. -/
def modToStage_f_zero [Fintype ι] (n : ℕ) :
    (modComplex I P n).X 0 ⟶ (stageComplexRestrict I P n).X 0 :=
  ModuleCat.ofHom (modToStageZeroLinear I P n)

/-- Degree-one component of the canonical comparison of complexes. -/
def modToStage_f_one [IsNoetherianRing A] [Fintype ι] (n : ℕ) :
    (modComplex I P n).X 1 ⟶ (stageComplexRestrict I P n).X 1 :=
  ModuleCat.ofHom (modToStageOneLinear I P n)

/-- The degree `1 → 0` square of the canonical comparison commutes. -/
private theorem modToStage_one_zero_comm [IsNoetherianRing A] [Fintype ι] (n : ℕ) :
    modToStage_f_one I P n ≫ (stageComplexRestrict I P n).d 1 0 =
      (modComplex I P n).d 1 0 ≫ modToStage_f_zero I P n :=
  sorry

/-- Higher components of the canonical comparison form commutative squares. -/
private theorem modToStage_succ_comm [IsNoetherianRing A] [Fintype ι] (n k : ℕ)
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
@[no_expose] def modToStage [IsNoetherianRing A] [Fintype ι] (n : ℕ) :
    modComplex I P n ⟶ stageComplexRestrict I P n :=
  ChainComplex.mkHom _ _ (modToStage_f_zero I P n) (modToStage_f_one I P n)
    (modToStage_one_zero_comm I P n)
    (fun k p ↦ ⟨0, modToStage_succ_comm I P n k p⟩)

/-- The degree-zero component of `modToStage` is the free-module comparison. -/
theorem modToStage_f_zero_eq [IsNoetherianRing A] [Fintype ι] (n : ℕ) :
    (modToStage I P n).f 0 = modToStage_f_zero I P n :=
  sorry

/-- The degree-one component of `modToStage` is the conormal comparison. -/
theorem modToStage_f_one_eq [IsNoetherianRing A] [Fintype ι] (n : ℕ) :
    (modToStage I P n).f 1 = modToStage_f_one I P n :=
  sorry

/-- Coordinatewise transition `(ι → B_{n+2}) → (ι → B_{n+1})`. -/
private def stageStepZeroOnFreeValue (n : ℕ) :
    (ι → (B ⧸ stageIdeal I (n + 1))) → (ι → (B ⧸ stageIdeal I n)) :=
  fun x i ↦ Submodule.factor (stageIdeal_succ_le I n) (x i)

/-- Coordinatewise quotient reduction preserves addition. -/
private theorem stageStepZeroOnFree_add (n : ℕ) (x y : (ι → (B ⧸ stageIdeal I (n + 1)))) :
    stageStepZeroOnFreeValue I n (x + y) =
      stageStepZeroOnFreeValue I n x + stageStepZeroOnFreeValue I n y := sorry

/-- Coordinatewise quotient reduction commutes with scalars. -/
private theorem stageStepZeroOnFree_smul (n : ℕ) (r : B) (x : (ι → (B ⧸ stageIdeal I (n + 1)))) :
    stageStepZeroOnFreeValue I n (r • x) = r • stageStepZeroOnFreeValue I n x := sorry

/-- Coordinatewise quotient reduction as a linear map. -/
@[no_expose] def stageStepZeroOnFree (n : ℕ) :
    (ι → (B ⧸ stageIdeal I (n + 1))) →ₗ[B] (ι → (B ⧸ stageIdeal I n)) where
  toFun := stageStepZeroOnFreeValue I n
  map_add' := stageStepZeroOnFree_add I n
  map_smul' := stageStepZeroOnFree_smul I n

/-- Coefficientwise polynomial transition `(A_{n+2})[x_ι] → (A_{n+1})[x_ι]`. -/
def stagePolyMap (n : ℕ) :
    MvPolynomial ι (stageBase I (n + 1)) →+* MvPolynomial ι (stageBase I n) :=
  MvPolynomial.map (algebraMap (stageBase I (n + 1)) (stageBase I n))

/-- The polynomial transition sends the stage kernel at `n+1` into the stage kernel at `n`. -/
theorem stagePolyMap_mem_ker (n : ℕ) {g : MvPolynomial ι (stageBase I (n + 1))}
    (hg : g ∈ stageKernel I P (n + 1)) :
    stagePolyMap I n g ∈ stageKernel I P n :=
  sorry

private def stageStepOneOnKerValue (n : ℕ) (g : stageKernel I P (n + 1)) :
    (ModuleCat.restrictScalars (stageAlgHom I P (n + 1)).toRingHom).obj
      ((ModuleCat.restrictScalars
        (Ideal.quotientMap (stageIdeal I n) (RingHom.id B) (stageIdeal_succ_le I n))).obj
          (stageConormal I P n)) :=
  (1 : B ⧸ stageIdeal I n) ⊗ₜ[MvPolynomial ι (stageBase I n), (stageAlgHom I P n).toRingHom]
    ((stageKernel I P n).toCotangent
      ⟨stagePolyMap I n g.val, stagePolyMap_mem_ker I P n g.property⟩)

/-- Reduction of stage relations to tensor-conormal classes preserves addition. -/
private theorem stageStepOneOnKer_add (n : ℕ) (g h : stageKernel I P (n + 1)) :
    stageStepOneOnKerValue I P n (g + h) =
      stageStepOneOnKerValue I P n g + stageStepOneOnKerValue I P n h := sorry

/-- Reduction of stage relations is linear for the source polynomial action. -/
private theorem stageStepOneOnKer_smul (n : ℕ)
    (r : MvPolynomial ι (stageBase I (n + 1))) (g : stageKernel I P (n + 1)) :
    stageStepOneOnKerValue I P n (r • g) = r • stageStepOneOnKerValue I P n g := sorry

/-- A stage relation maps to one tensor the conormal class of its reduction. -/
@[no_expose] def stageStepOneOnKer (n : ℕ) :
    stageKernel I P (n + 1) →ₗ[MvPolynomial ι (stageBase I (n + 1))]
      (ModuleCat.restrictScalars (stageAlgHom I P (n + 1)).toRingHom).obj
      ((ModuleCat.restrictScalars
        (Ideal.quotientMap (stageIdeal I n) (RingHom.id B) (stageIdeal_succ_le I n))).obj
          (stageConormal I P n)) where
  toFun := stageStepOneOnKerValue I P n
  map_add' := stageStepOneOnKer_add I P n
  map_smul' := stageStepOneOnKer_smul I P n

/-- Reduction of stage relations annihilates the square of the source kernel. -/
theorem stageStepOneOnKer_square (n : ℕ) :
    (stageKernel I P (n + 1) • ⊤ :
      Submodule (MvPolynomial ι (stageBase I (n + 1))) (stageKernel I P (n + 1))) ≤
        LinearMap.ker (stageStepOneOnKer I P n) := sorry

private def conormalDescend {R S : Type u} [CommRing R] [CommRing S]
    (J : Ideal R) (f : R →+* S) (M : ModuleCat S)
    (g : J →ₗ[R] (ModuleCat.restrictScalars f).obj M)
    (hg : (J • ⊤ : Submodule R J) ≤ LinearMap.ker g) :
    ModuleCat.of R J.Cotangent ⟶ (ModuleCat.restrictScalars f).obj M :=
  ModuleCat.ofHom (X := ModuleCat.of R J.Cotangent)
    (Y := (ModuleCat.restrictScalars f).obj M) (Submodule.liftQ _ g hg)

private def stageStepCotangentMap (n : ℕ) :
    ModuleCat.of (MvPolynomial ι (stageBase I (n + 1)))
      (stageKernel I P (n + 1)).Cotangent ⟶
    (ModuleCat.restrictScalars (stageAlgHom I P (n + 1)).toRingHom).obj
      ((ModuleCat.restrictScalars
        (Ideal.quotientMap (stageIdeal I n) (RingHom.id B) (stageIdeal_succ_le I n))).obj
          (stageConormal I P n)) :=
  conormalDescend (stageKernel I P (n + 1)) (stageAlgHom I P (n + 1)).toRingHom
    ((ModuleCat.restrictScalars
      (Ideal.quotientMap (stageIdeal I n) (RingHom.id B) (stageIdeal_succ_le I n))).obj
        (stageConormal I P n))
    (stageStepOneOnKer I P n) (stageStepOneOnKer_square I P n)

private def stageStepTensorMap (n : ℕ) :
    stageConormal I P (n + 1) ⟶
      (ModuleCat.restrictScalars
        (Ideal.quotientMap (stageIdeal I n) (RingHom.id B) (stageIdeal_succ_le I n))).obj
          (stageConormal I P n) :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (stageAlgHom I P (n + 1)).toRingHom (stageStepCotangentMap I P n)

private def stageStepOneValue (n : ℕ) (x : stageConormal I P (n + 1)) :
    (ModuleCat.restrictScalars (algebraMap B (B ⧸ stageIdeal I n))).obj
      (stageConormal I P n) :=
  (stageStepTensorMap I P n).hom x

/-- The tensor-conormal transition preserves addition. -/
private theorem stageStepOneLinear_add (n : ℕ) (x y : stageConormal I P (n + 1)) :
    stageStepOneValue I P n (x + y) =
      stageStepOneValue I P n x + stageStepOneValue I P n y := sorry

/-- The tensor-conormal transition is `B`-linear. -/
private theorem stageStepOneLinear_smul (n : ℕ) (r : B)
    (x : (ModuleCat.restrictScalars (algebraMap B (B ⧸ stageIdeal I (n + 1)))).obj
      (stageConormal I P (n + 1))) :
    stageStepOneValue I P n (r • x) = r • stageStepOneValue I P n x := sorry

/-- The canonical transition between stage tensor-conormal modules, restricted to `B`. -/
@[no_expose] def stageStepOneLinear (n : ℕ) :
    (ModuleCat.restrictScalars (algebraMap B (B ⧸ stageIdeal I (n + 1)))).obj
      (stageConormal I P (n + 1)) →ₗ[B]
    (ModuleCat.restrictScalars (algebraMap B (B ⧸ stageIdeal I n))).obj (stageConormal I P n) where
  toFun := stageStepOneValue I P n
  map_add' := stageStepOneLinear_add I P n
  map_smul' := stageStepOneLinear_smul I P n

/-- Degree-zero component of the stage transition of restricted complexes. -/
def stageStep_f_zero [Fintype ι] (n : ℕ) :
    (stageComplexRestrict I P (n + 1)).X 0 ⟶ (stageComplexRestrict I P n).X 0 :=
  ModuleCat.ofHom (stageStepZeroOnFree I n)

/-- Degree-one component of the stage transition of restricted complexes. -/
def stageStep_f_one [Fintype ι] (n : ℕ) :
    (stageComplexRestrict I P (n + 1)).X 1 ⟶ (stageComplexRestrict I P n).X 1 :=
  ModuleCat.ofHom (stageStepOneLinear I P n)

/-- The degree `1 → 0` square of the stage transition commutes. -/
private theorem stageStep_one_zero_comm [Fintype ι] (n : ℕ) :
    stageStep_f_one I P n ≫ (stageComplexRestrict I P n).d 1 0 =
      (stageComplexRestrict I P (n + 1)).d 1 0 ≫ stageStep_f_zero I P n :=
  sorry

/-- Higher components of the stage transition form commutative squares. -/
private theorem stageStep_succ_comm [Fintype ι] (n k : ℕ)
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
@[no_expose] def stageSystemStep [Fintype ι] (n : ℕ) :
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
theorem modToStage_naturality [IsNoetherianRing A] [Fintype ι] (n : ℕ) :
    (modSystem I P).map (homOfLE (Nat.le_add_right n 1)).op ≫ modToStage I P n =
      modToStage I P (n + 1) ≫
        (stageSystem I P).map (homOfLE (Nat.le_add_right n 1)).op :=
  sorry

/-- The canonical comparison as a morphism of inverse systems of complexes. -/
def modToStageNatTrans [IsNoetherianRing A] [Fintype ι] : modSystem I P ⟶ stageSystem I P :=
  NatTrans.ofOpSequence (modToStage I P) (modToStage_naturality I P)

/-- Components of `modToStageNatTrans` are the chain maps `modToStage`. -/
theorem modToStageNatTrans_app [IsNoetherianRing A] [Fintype ι] (n : ℕ) :
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
def modToStageDerivedNatTrans [IsNoetherianRing A] [Fintype ι] :
    modDerivedSystem I P ⟶ stageDerivedSystem I P :=
  Functor.whiskerRight
    (Functor.whiskerRight (modToStageNatTrans I P)
      (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat B)))
    DerivedCategory.Q

/-- The sequential pro-morphism in `D(B)` represented by the derived comparison. -/
def modToStageDerivedHom [IsNoetherianRing A] [Fintype ι] :
    Pro.SequentialHom (modDerivedSystem I P) (stageDerivedSystem I P) :=
  Pro.SequentialHom.ofNatTrans (modToStageDerivedNatTrans I P)

/-- The derived comparison representative uses the identity reindexing. -/
theorem modToStageDerivedHom_reindex [IsNoetherianRing A] [Fintype ι] :
    (modToStageDerivedHom I P).reindex = OrderHom.id :=
  sorry

end Algebra.NaiveCotangent.Adic
