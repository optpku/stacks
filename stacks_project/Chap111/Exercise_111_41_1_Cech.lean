/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TopSections
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.Topology.Presheaf.Cech.TermIso
public import stacks_project.Chap111.Exercise_111_41_1_Cover

/-!
# Čech cohomology of `𝒪` on the doubled affine line

Coverwise `check H¹(𝒰, 𝒪)` is `moduleCechCohomology` of the unit module on `chartCover`. The
computational model is the Laurent quotient `k[T;T⁻¹] / k[X]`, with candidate basis the classes of
`T ^ (-n)` for `n ≥ 1`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.DoubledOrigin AlgebraicGeometry.RingedSpace
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite SheafOfModules
open TopologicalSpace
open scoped AlgebraicGeometry LaurentPolynomial

noncomputable section

universe u

namespace AlgebraicGeometry.DoubledOrigin

variable (k : Type u) [Field k]

/-- Coverwise Čech cohomology `check H¹(𝒰, 𝒪)` of the structure sheaf on the two-chart cover of
the affine line with doubled origin. -/
abbrev cechH1 : AddCommGrpCat.{u} :=
  moduleCechCohomology (chartCoverULift k)
    (SheafOfModules.unit (scheme k 1).toRingedSpace.ringCatSheaf) 1

/-- The polynomial submodule of Laurent polynomials, i.e. the image of `k[X] → k[T;T⁻¹]`. -/
abbrev polynomialRange : Submodule k (LaurentPolynomial k) :=
  LinearMap.range (Polynomial.toLaurentAlg : Polynomial k →ₐ[k] LaurentPolynomial k).toLinearMap

/-- The Laurent quotient `k[T;T⁻¹] / k[X]`, the computational model of `check H¹(𝒰, 𝒪)`. -/
abbrev laurentQuotient : Type u :=
  LaurentPolynomial k ⧸ polynomialRange k

/-- The class of a Laurent polynomial in the quotient by polynomials. -/
def laurentQuotientMk (f : LaurentPolynomial k) : laurentQuotient k :=
  Submodule.Quotient.mk f

/-- Polynomials become zero in the Laurent quotient. -/
theorem laurentQuotientMk_toLaurent (p : Polynomial k) :
    laurentQuotientMk k (Polynomial.toLaurent p) = 0 :=
  sorry

/-- Candidate basis vectors: the classes of `T ^ (-n)` for positive `n`. -/
def laurentQuotientBasis : {n : ℕ // 0 < n} → laurentQuotient k :=
  fun n ↦ laurentQuotientMk k (LaurentPolynomial.T (-(n : ℤ)))

/-- The `n`-th basis vector is the class of `T ^ (-n)`. -/
theorem laurentQuotientBasis_apply (n : {n : ℕ // 0 < n}) :
    laurentQuotientBasis k n = laurentQuotientMk k (LaurentPolynomial.T (-(n : ℤ))) :=
  sorry

/-- Multiplication by a global constant of `k` as an endomorphism of the structure sheaf. -/
def unitMul (a : k) :
    SheafOfModules.unit (scheme k 1).toRingedSpace.ringCatSheaf ⟶
      SheafOfModules.unit (scheme k 1).toRingedSpace.ringCatSheaf :=
  topSectionMorphism
    (SheafOfModules.unit (scheme k 1).toRingedSpace.ringCatSheaf)
    (Scheme.Hom.globalSectionsMap (toBase k 1) a)

/-- Multiplication by `1` is the identity on the structure sheaf. -/
theorem unitMul_one :
    unitMul k 1 = 𝟙 (SheafOfModules.unit (scheme k 1).toRingedSpace.ringCatSheaf) :=
  sorry

/-- The carrier of coverwise `check H¹(𝒰, 𝒪)`. -/
abbrev cechH1Carrier : Type u :=
  cechH1 k

/-- The carrier of `cechH1` is the underlying type of the Čech cohomology group. -/
theorem cechH1Carrier_eq :
    cechH1Carrier k = (cechH1 k : Type u) :=
  sorry

/-- Scalar multiplication on `check H¹(𝒰, 𝒪)` by a global constant of `k`. -/
def cechH1Smul (a : k) (x : cechH1Carrier k) : cechH1Carrier k :=
  (moduleCechCohomologyFunctor (chartCoverULift k) 1).map (unitMul k a) x

/-- The `k`-module structure on `check H¹(𝒰, 𝒪)` whose scalar multiplication is by global
constants. -/
noncomputable instance cechH1Module : Module k (cechH1Carrier k) where
  smul := cechH1Smul k
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

/-- Scalar multiplication on `cechH1` is `cechH1Smul`. -/
theorem cechH1Module_smul (a : k) (x : cechH1Carrier k) :
    a • x = cechH1Smul k a x :=
  sorry

/-- The underlying additive presheaf of the structure sheaf on the doubled line. -/
abbrev unitUnderlyingPresheaf :
    (scheme k 1).carrier.Presheaf AddCommGrpCat.{u} :=
  (moduleUnderlyingPresheaf (scheme k 1).toRingedSpace).obj
    (SheafOfModules.unit (scheme k 1).toRingedSpace.ringCatSheaf)

/-- Unfolding of `unitUnderlyingPresheaf`. -/
theorem unitUnderlyingPresheaf_eq :
    unitUnderlyingPresheaf k =
      (moduleUnderlyingPresheaf (scheme k 1).toRingedSpace).obj
        (SheafOfModules.unit (scheme k 1).toRingedSpace.ringCatSheaf) :=
  sorry

/-- The Čech complex of `𝒪` on the two-chart cover. -/
abbrev unitCechComplex :
    CochainComplex AddCommGrpCat.{u} ℕ :=
  moduleCechComplex (chartCoverULift k)
    (SheafOfModules.unit (scheme k 1).toRingedSpace.ringCatSheaf)

/-- Unfolding of `unitCechComplex`. -/
theorem unitCechComplex_eq :
    unitCechComplex k =
      moduleCechComplex (chartCoverULift k)
        (SheafOfModules.unit (scheme k 1).toRingedSpace.ringCatSheaf) :=
  sorry

/-- The ordered pair of chart indices `(0, 1)`. -/
def mixed01 : Fin 2 → ULift.{u} (Fin 2) :=
  ULift.up

/-- The first index of `mixed01` is the left chart. -/
theorem mixed01_zero : mixed01 0 = ULift.up 0 :=
  sorry

/-- The second index of `mixed01` is the right chart. -/
theorem mixed01_one : mixed01 1 = ULift.up 1 :=
  sorry

/-- The ordered pair of chart indices `(1, 0)`. -/
def mixed10 : Fin 2 → ULift.{u} (Fin 2) :=
  fun i ↦ ULift.up (1 - i)

/-- The first index of `mixed10` is the right chart. -/
theorem mixed10_zero : mixed10 0 = ULift.up 1 :=
  sorry

/-- The second index of `mixed10` is the left chart. -/
theorem mixed10_one : mixed10 1 = ULift.up 0 :=
  sorry

/-- Restriction of an overlap section to the mixed Čech intersection indexed by `(0, 1)`. -/
def overlapRestrictMixed01 (α : Γ(scheme k 1, chartOverlap k)) :
    (unitUnderlyingPresheaf k).obj
      (op (TopCat.Presheaf.Cech.intersection (chartCoverULift k) mixed01)) :=
  (unitUnderlyingPresheaf k).map
    (homOfLE
      (le_inf (iInf_le (fun a ↦ chartCoverULift k (mixed01 a)) 0)
        (iInf_le (fun a ↦ chartCoverULift k (mixed01 a)) 1))).op
    α

/-- Restriction of an overlap section to the mixed Čech intersection indexed by `(1, 0)`. -/
def overlapRestrictMixed10 (α : Γ(scheme k 1, chartOverlap k)) :
    (unitUnderlyingPresheaf k).obj
      (op (TopCat.Presheaf.Cech.intersection (chartCoverULift k) mixed10)) :=
  (unitUnderlyingPresheaf k).map
    (homOfLE
      (le_inf (iInf_le (fun a ↦ chartCoverULift k (mixed10 a)) 1)
        (iInf_le (fun a ↦ chartCoverULift k (mixed10 a)) 0))).op
    α

/-- Evaluating the `(0, 1)` restriction recovers the overlap section on that mixed intersection. -/
theorem overlapRestrictMixed01_apply (α : Γ(scheme k 1, chartOverlap k)) :
    overlapRestrictMixed01 k α =
      (unitUnderlyingPresheaf k).map
        (homOfLE
          (le_inf (iInf_le (fun a ↦ chartCoverULift k (mixed01 a)) 0)
            (iInf_le (fun a ↦ chartCoverULift k (mixed01 a)) 1))).op
        α :=
  sorry

/-- Evaluating the `(1, 0)` restriction recovers the overlap section on that mixed intersection. -/
theorem overlapRestrictMixed10_apply (α : Γ(scheme k 1, chartOverlap k)) :
    overlapRestrictMixed10 k α =
      (unitUnderlyingPresheaf k).map
        (homOfLE
          (le_inf (iInf_le (fun a ↦ chartCoverULift k (mixed10 a)) 1)
            (iInf_le (fun a ↦ chartCoverULift k (mixed10 a)) 0))).op
        α :=
  sorry

/-- The Čech 1-cochain on `𝒰` with overlap value `α` on mixed pairs and `0` on repeated indices. -/
def overlapCocycle (α : Γ(scheme k 1, chartOverlap k)) :
    TopCat.Presheaf.Cech.term (chartCoverULift k) (unitUnderlyingPresheaf k) 1 :=
  fun σ ↦
    if h : σ = mixed01 then
      h ▸ overlapRestrictMixed01 k α
    else if h' : σ = mixed10 then
      h' ▸ (-overlapRestrictMixed10 k α)
    else
      0

/-- The overlap cocycle evaluates to the `(0, 1)` restriction on `mixed01`. -/
theorem overlapCocycle_mixed01 (α : Γ(scheme k 1, chartOverlap k)) :
    overlapCocycle k α mixed01 = overlapRestrictMixed01 k α :=
  sorry

/-- The overlap cocycle evaluates to the negated `(1, 0)` restriction on `mixed10`. -/
theorem overlapCocycle_mixed10 (α : Γ(scheme k 1, chartOverlap k)) :
    overlapCocycle k α mixed10 = -overlapRestrictMixed10 k α :=
  sorry

/-- The coverwise Čech class of an overlap section on the two-chart identity glueing. -/
def cechClassOfOverlapSection (α : Γ(scheme k 1, chartOverlap k)) : cechH1 k :=
  (unitCechComplex k).homologyπ 1
    (Function.invFun (fun z ↦ (unitCechComplex k).iCycles 1 z)
      ((TopCat.Presheaf.Cech.termIso (chartCoverULift k) (unitUnderlyingPresheaf k) 1).inv
        (overlapCocycle k α)))

/-- The Čech class of the zero overlap section vanishes. -/
theorem cechClassOfOverlapSection_zero :
    cechClassOfOverlapSection k 0 = 0 :=
  sorry

/-- An overlap section `α` represents the Čech class `c` on the two-chart cover `𝒰`. -/
def IsOverlapCocycleClass (α : Γ(scheme k 1, chartOverlap k)) (c : cechH1 k) : Prop :=
  cechClassOfOverlapSection k α = c

/-- Unfolding of `IsOverlapCocycleClass`. -/
theorem isOverlapCocycleClass_iff (α : Γ(scheme k 1, chartOverlap k)) (c : cechH1 k) :
    IsOverlapCocycleClass k α c ↔ cechClassOfOverlapSection k α = c :=
  sorry

/-- Coverwise `check H¹(𝒰, 𝒪)` is isomorphic to the Laurent quotient as abelian groups. -/
theorem cechH1_isIsomorphic_laurentQuotient :
    IsIsomorphic (cechH1 k) (AddCommGrpCat.of (laurentQuotient k)) :=
  sorry

/-- The classes of `T ^ (-n)` for `n ≥ 1` are linearly independent over `k`. -/
theorem laurentQuotientBasis_linearIndependent :
    LinearIndependent k (laurentQuotientBasis k) :=
  sorry

/-- The classes of `T ^ (-n)` for `n ≥ 1` span the Laurent quotient. -/
theorem laurentQuotientBasis_span :
    Submodule.span k (Set.range (laurentQuotientBasis k)) = ⊤ :=
  sorry

/-- The classes of `T ^ (-n)` for `n ≥ 1` form a `k`-basis of the Laurent quotient. -/
theorem laurentQuotientBasis_bijective :
    Function.Bijective (Finsupp.linearCombination k (laurentQuotientBasis k)) :=
  sorry

end AlgebraicGeometry.DoubledOrigin
