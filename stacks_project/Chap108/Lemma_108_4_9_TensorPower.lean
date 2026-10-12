/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import stacks_project.Chap108.Lemma_108_4_9_InternalHomClosed
public import stacks_project.Chap108.Lemma_108_4_9_StructureSheafResolution
public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Closed
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Exact
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation
public import stacks_project.Chap75.Lemma_75_5_6_Instances

/-!
# Integer tensor powers of derived modules

Derived tensor powers `E^{⊗ n}` of an object of `D(𝒪_X)`, including negative
exponents via the sheafy derived dual `RHom(E, 𝒪_X[0])`, and the finite-family map
`(n₁, …, nᵣ) ↦ ⨂ᵢ Eᵢ^{⊗ nᵢ}` on `ℤ^{⊕ r}`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.DerivedCategory CategoryTheory.DerivedCategory.DerivedTensor
open SheafOfModules.RingedSite
open scoped CategoryTheory.DerivedCategory.DerivedTensor ZeroObject

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

/-- The canonical symmetry on `𝒪_X`-modules, specialized from the commutative small
étale ringed site. -/
noncomputable instance instSymmetricCategory (X : AlgebraicSpace S) :
    SymmetricCategory X.Modules :=
  Modules.DirectTensorComparison.symmetric X

end AlgebraicGeometry.AlgebraicSpace.Modules

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The degree-zero object `𝒪_X[0]` in `D(𝒪_X)`. -/
noncomputable def derivedUnit (X : AlgebraicSpace S) : ModuleDerived X :=
  (DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj (𝟙_ X.Modules)

/-- `derivedUnit X` is the image of the monoidal unit of `X.Modules` under the
degree-zero single functor. -/
theorem derivedUnit_eq (X : AlgebraicSpace S) :
    derivedUnit X =
      (DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj (𝟙_ X.Modules) :=
  sorry

/-- A specified cochain representative of `derivedUnit X`, namely the single complex
`𝒪_X[0]`. -/
noncomputable def derivedUnitRepresentative (X : AlgebraicSpace S) :
    CochainComplex X.Modules ℤ :=
  (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj (𝟙_ X.Modules)

/-- `derivedUnit X` is the derived image of `derivedUnitRepresentative X`. -/
theorem derivedUnit_Q_representative (X : AlgebraicSpace S) :
    derivedUnit X = DerivedCategory.Q.obj (derivedUnitRepresentative X) :=
  sorry

/-- Nonnegative derived tensor powers of `E`, based at `derivedUnit`. -/
noncomputable def tensorPowerNat (E : ModuleDerived X) : ℕ → ModuleDerived X :=
  Nat.rec (derivedUnit X) (fun _ acc ↦ DerivedTensor.Right.obj acc E)

/-- The zeroth nonnegative derived tensor power is `derivedUnit`. -/
theorem tensorPowerNat_zero (E : ModuleDerived X) :
    tensorPowerNat E 0 = derivedUnit X :=
  sorry

/-- Successor nonnegative derived tensor powers are derived tensor with `E`. -/
theorem tensorPowerNat_succ (E : ModuleDerived X) (n : ℕ) :
    tensorPowerNat E (n + 1) = DerivedTensor.Right.obj (tensorPowerNat E n) E :=
  sorry

/-- The index type `ℤ^{⊕ r}` at the universe of `Scheme.{u}` and of numerical
invariants. -/
abbrev tensorPowerIndex (r : ℕ) : Type u :=
  ULift.{u} (Fin r → ℤ)

/-- Downplaying the universe embedding of a multiindex recovers the function
`Fin r → ℤ`. -/
theorem tensorPowerIndex_up (r : ℕ) (n : Fin r → ℤ) :
    (ULift.up n : tensorPowerIndex r).down = n :=
  sorry

/-- The degree-zero structure sheaf is perfect. -/
theorem isPerfect_derivedUnit :
    ModuleDerived.IsPerfect (derivedUnit X) :=
  sorry

/-- Nonnegative derived tensor powers of a perfect object are perfect. -/
theorem isPerfect_tensorPowerNat (E : ModuleDerived X)
    (hE : ModuleDerived.IsPerfect E) (n : ℕ) :
    ModuleDerived.IsPerfect (tensorPowerNat E n) :=
  sorry

/-- A cochain representative of an object of `D(𝒪_X)`. -/
noncomputable def cochainRepresentative (E : ModuleDerived X) :
    CochainComplex X.Modules ℤ :=
  DerivedCategory.Q.objPreimage E

/-- `cochainRepresentative E` is the essential-surjectivity preimage of `E` under
`DerivedCategory.Q`. -/
theorem cochainRepresentative_eq (E : ModuleDerived X) :
    cochainRepresentative E = DerivedCategory.Q.objPreimage E :=
  sorry

/-- Pass a cochain complex of `𝒪_X`-modules to the commutative presentation. -/
noncomputable def toCommCochain (K : CochainComplex X.Modules ℤ) :
    CochainComplex (commModules X) ℤ where
  X n := (toCommModules X).obj (K.X n)
  d i j := (toCommModules X).map (K.d i j)
  shape := sorry
  d_comp_d' := sorry

/-- Terms of `toCommCochain K` are the commutative presentation of the terms of `K`. -/
theorem toCommCochain_X (K : CochainComplex X.Modules ℤ) (n : ℤ) :
    (toCommCochain K).X n = (toCommModules X).obj (K.X n) :=
  sorry

/-- The certified actual replacement of the structure-sheaf unit in the original category. -/
noncomputable abbrev derivedUnitInjectiveComplex (X : AlgebraicSpace S) :
    CochainComplex X.Modules ℤ :=
  AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.StructureSheaf.unitReplacement X

/-- The actual comparison from the source's precise degree-zero structure-sheaf complex. -/
noncomputable abbrev derivedUnitInjectiveι (X : AlgebraicSpace S) :
    derivedUnitRepresentative X ⟶ derivedUnitInjectiveComplex X :=
  AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.StructureSheaf.unitReplacementMap X

theorem derivedUnitInjectiveComplex_isKInjective (X : AlgebraicSpace S) :
    (derivedUnitInjectiveComplex X).IsKInjective :=
  AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.StructureSheaf.unitReplacementKInjective X

theorem derivedUnitInjectiveι_quasiIso (X : AlgebraicSpace S) :
    QuasiIso (derivedUnitInjectiveι X) :=
  AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.StructureSheaf.unitReplacementQuasiIso X

/-- Use the small realization of the canonical slice-morphism internal Hom. -/
-- Local instance justification (proof-local temporary data): Select the certified small-carrier realization of local sheaf Hom at the original universe.
local instance smallMonoidalClosed (X : AlgebraicSpace S) : MonoidalClosed (commModules X) :=
  AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.InternalHom.monoidalClosed X

/-- Actual source and target of the sheafy derived Hom. -/
noncomputable def dualSource (E : ModuleDerived X) : CochainComplex (commModules X) ℤ :=
  toCommCochain (cochainRepresentative E)

noncomputable def dualTarget (X : AlgebraicSpace S) : CochainComplex (commModules X) ℤ :=
  toCommCochain (derivedUnitInjectiveComplex X)

/-- The standard cochain internal Hom; its degreewise sections are certified-small local
morphisms on slice sites, and its differential is the canonical graded commutator. -/
noncomputable def dualCommCochain (E : ModuleDerived X) : CochainComplex (commModules X) ℤ :=
  CategoryTheory.CochainComplex.InternalHom.obj (dualSource E) (dualTarget X)

/-- Return through the existing commutative-presentation equivalence, without universe unlift. -/
noncomputable def ofCommCochain (K : CochainComplex (commModules X) ℤ) :
    CochainComplex X.Modules ℤ where
  X n := (ofCommModules X).obj (K.X n)
  d i j := (ofCommModules X).map (K.d i j)
  shape := by sorry
  d_comp_d' := by sorry

noncomputable def dualCochain (E : ModuleDerived X) : CochainComplex X.Modules ℤ :=
  ofCommCochain (dualCommCochain E)

/-- The sheafy derived dual, represented by the canonical Hom complex into a certified
K-injective replacement of O_X[0], all in the original module universe. -/
noncomputable def dual (E : ModuleDerived X) : ModuleDerived X :=
  DerivedCategory.Q.obj (dualCochain E)

theorem dual_eq (E : ModuleDerived X) :
    dual E = DerivedCategory.Q.obj (ofCommCochain
      (CategoryTheory.CochainComplex.InternalHom.obj (dualSource E) (dualTarget X))) := rfl

theorem dualCommCochain_d (E : ModuleDerived X) (n : ℤ) :
    (dualCommCochain E).d n (n + 1) =
      CategoryTheory.CochainComplex.InternalHom.differential (dualSource E) (dualTarget X) n :=
  CochainComplex.of_d _ _ n

/-- The sheafy dual of a perfect object is perfect. -/
theorem isPerfect_dual (E : ModuleDerived X)
    (hE : ModuleDerived.IsPerfect E) :
    ModuleDerived.IsPerfect (dual E) :=
  sorry

/-- Integral derived tensor powers of `E`, using the dual for negative exponents. -/
noncomputable def tensorPowerInt (E : ModuleDerived X) (n : ℤ) : ModuleDerived X :=
  match n with
  | Int.ofNat k => tensorPowerNat E k
  | Int.negSucc k => tensorPowerNat (dual E) (k + 1)

/-- Nonnegative integral derived tensor powers agree with `tensorPowerNat`. -/
theorem tensorPowerInt_ofNat (E : ModuleDerived X) (n : ℕ) :
    tensorPowerInt E n = tensorPowerNat E n :=
  sorry

/-- Negative integral derived tensor powers are nonnegative powers of the dual. -/
theorem tensorPowerInt_negSucc (E : ModuleDerived X) (n : ℕ) :
    tensorPowerInt E (Int.negSucc n) = tensorPowerNat (dual E) (n + 1) :=
  sorry

/-- The family `(n₁, …, nᵣ) ↦ ⨂ᵢ Eᵢ^{⊗ nᵢ}` on `tensorPowerIndex r`. -/
noncomputable def tensorPowerFamily {r : ℕ} (E : Fin r → ModuleDerived X) :
    tensorPowerIndex r → ModuleDerived X :=
  fun n ↦
    (List.ofFn fun i : Fin r ↦ i).foldl
      (fun acc i ↦ DerivedTensor.Right.obj acc (tensorPowerInt (E i) (n.down i)))
      (derivedUnit X)

/-- Evaluating `tensorPowerFamily` at `ULift.up n` is
`derivedUnit ⊗ E 0 ^{⊗ n 0} ⊗ ⋯ ⊗ E (r-1) ^{⊗ n (r-1)}` in source list order. -/
theorem tensorPowerFamily_apply {r : ℕ} (E : Fin r → ModuleDerived X)
    (n : Fin r → ℤ) :
    tensorPowerFamily E (ULift.up n) =
      (List.ofFn fun i : Fin r ↦ i).foldl
        (fun acc i ↦ DerivedTensor.Right.obj acc (tensorPowerInt (E i) (n i)))
        (derivedUnit X) :=
  sorry

/-- Integral derived tensor powers of a perfect object are perfect. -/
theorem isPerfect_tensorPowerInt (E : ModuleDerived X)
    (hE : ModuleDerived.IsPerfect E) (n : ℤ) :
    ModuleDerived.IsPerfect (tensorPowerInt E n) :=
  sorry

/-- Tensor-power families of perfect objects remain perfect at every index. -/
theorem isPerfect_tensorPowerFamily {r : ℕ} (E : Fin r → ModuleDerived X)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) (n : tensorPowerIndex r) :
    ModuleDerived.IsPerfect (tensorPowerFamily E n) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
