module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import ReasLib.Algebra.Homology.DifferentialGradedModule.DifferentialGraded
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Forget
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Homotopy
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Left
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The Regular Differential Graded Module

A cochain differential graded algebra is canonically a right module over itself.  Its integer
shifts are the free rank-one differential graded modules.  This leaf exposes their universal
mapping properties in the closed and homotopy categories.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory
open DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

namespace CochainDGAlgebra

variable {R : Type u} [CommRing R]

/-- The unit of a cochain differential graded algebra is a cycle in degree zero. -/
theorem d_one_eq_zero (A : CochainDGAlgebra.{u, v} R) : A.d 0 A.one = 0 := sorry

/-- A cochain differential graded algebra regarded as its canonical regular right module. -/
@[stacks 09K1 "regular differential graded module"]
noncomputable def regularModule (A : CochainDGAlgebra.{u, v} R) : DifferentialGradedModule.{u, v} A where
  X := A.X
  d := fun n ↦ ModuleCat.Hom.hom (A.d n)
  smul := A.mul
  d_sq := sorry
  smul_one := sorry
  smul_mul := sorry
  comm_d := sorry

/-- The degree-`n` component of the regular module is the degree-`n` component of the algebra. -/
@[simp]
theorem regularModule_X (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    A.regularModule.X n = A.X n := sorry

/-- The differential of the regular module is the algebra differential. -/
@[simp]
theorem regularModule_d (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    A.regularModule.d n = ModuleCat.Hom.hom (A.d n) := sorry

/-- The right action of the regular module is multiplication in the algebra. -/
@[simp]
theorem regularModule_smul (A : CochainDGAlgebra.{u, v} R) (p i : ℤ) :
    A.regularModule.smul p i = A.mul p i := sorry

/-- Forgetting the regular module to a cochain complex recovers the underlying algebra complex. -/
@[simp]
theorem regularModule_toCochainComplex (A : CochainDGAlgebra.{u, v} R) :
    A.regularModule.toCochainComplex = A.toCochainComplex := sorry

/-- A cochain differential graded algebra regarded as its canonical regular left module. -/
@[stacks 0FQD "regular left differential graded module"]
def leftRegularModule (A : CochainDGAlgebra.{u, v} R) :
    LeftDifferentialGradedModule.{u, v} A where
  X := A.X
  d n := ModuleCat.Hom.hom (A.d n)
  smul := A.mul
  d_sq := sorry
  smul_one := sorry
  smul_mul := sorry
  comm_d := sorry

/-- The degree-`n` component of the regular left module is the degree-`n` component of the DGA. -/
@[simp]
theorem leftRegularModule_X (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    A.leftRegularModule.X n = A.X n := sorry

/-- The differential of the regular left module is the DGA differential. -/
@[simp]
theorem leftRegularModule_d (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    A.leftRegularModule.d n = ModuleCat.Hom.hom (A.d n) := sorry

/-- The action on the regular left module is multiplication in the DGA. -/
@[simp]
theorem leftRegularModule_smul (A : CochainDGAlgebra.{u, v} R) (i p : ℤ) :
    A.leftRegularModule.smul i p = A.mul i p := sorry

namespace RegularModule

/-- The shift of the regular module, viewed in the category of closed degree-zero maps. -/
abbrev shiftComp (A : CochainDGAlgebra.{u, v} R) (k : ℤ) :
    Comp R (DifferentialGradedModule.{u, v} A) :=
  ⟨A.regularModule[k]⟩

/-- The shift of the regular module, viewed in the differential graded homotopy category. -/
abbrev shiftK (A : CochainDGAlgebra.{u, v} R) (k : ℤ) :
    K R (DifferentialGradedModule.{u, v} A) :=
  ⟨A.regularModule[k]⟩

/-- The canonical unit generator of the shifted regular module, in degree `-k`. -/
def shiftedUnit (A : CochainDGAlgebra.{u, v} R) (k : ℤ) : (A.regularModule[k]).X (-k) :=
  cast (congrArg (fun n : ℤ ↦ (A.X n : Type v)) (neg_add_cancel k).symm) A.one

/-- The shifted unit generator is closed. -/
theorem shiftedUnit_closed (A : CochainDGAlgebra.{u, v} R) (k : ℤ) :
    (A.regularModule[k]).d (-k) (shiftedUnit A k) = 0 := sorry

/-- The target degree obtained by acting on the shifted unit is the original algebra degree. -/
theorem shiftedUnitActionIndex (k n : ℤ) : ((-k : ℤ) + (n + k)) + k = n + k := sorry

/-- The shifted unit generates every homogeneous component of the shifted regular module. -/
theorem shiftedUnit_smul (A : CochainDGAlgebra.{u, v} R) (k n : ℤ) (x : A.X (n + k)) :
    cast
      (congrArg (fun m : ℤ ↦ (A.X m : Type v))
        (shiftedUnitActionIndex k n))
      ((A.regularModule[k]).smul (-k) (n + k) (shiftedUnit A k) x) = x := sorry

/-- Evaluate a closed map from a shifted regular module on its unit generator. -/
noncomputable def cycleOfHom (A : CochainDGAlgebra.{u, v} R)
    (M : DifferentialGradedModule.{u, v} A) (k : ℤ)
    (f : shiftComp A k ⟶ (⟨M⟩ : Comp R (DifferentialGradedModule.{u, v} A))) :
    M.cycles (-k) :=
  (M.toCochainComplex.sc (-k)).moduleCatCyclesIso.inv
    ⟨cast (congrArg (fun n : ℤ ↦ (M.X n : Type v)) (add_zero (-k)))
      (f.val.1 (-k) (shiftedUnit A k)), sorry⟩

/-- The underlying cycle of `cycleOfHom` is evaluation on the shifted unit. -/
@[simp]
theorem cycleOfHom_iCycles (A : CochainDGAlgebra.{u, v} R)
    (M : DifferentialGradedModule.{u, v} A) (k : ℤ)
    (f : shiftComp A k ⟶ (⟨M⟩ : Comp R (DifferentialGradedModule.{u, v} A))) :
    ModuleCat.Hom.hom (M.iCycles (-k)) (cycleOfHom A M k f) =
      cast (congrArg (fun n : ℤ ↦ (M.X n : Type v)) (add_zero (-k)))
        (f.val.1 (-k) (shiftedUnit A k)) := sorry

/-- Evaluation on the shifted unit as an `R`-linear map from closed morphisms to cycles. -/
noncomputable def cycleEvaluation (A : CochainDGAlgebra.{u, v} R)
    (M : DifferentialGradedModule.{u, v} A) (k : ℤ) :
    (shiftComp A k ⟶ (⟨M⟩ : Comp R (DifferentialGradedModule.{u, v} A))) →ₗ[R]
      M.cycles (-k) where
  toFun := cycleOfHom A M k
  map_add' := sorry
  map_smul' := sorry

/-- Applying the linear evaluation map agrees with `cycleOfHom`. -/
@[simp]
theorem cycleEvaluation_apply (A : CochainDGAlgebra.{u, v} R)
    (M : DifferentialGradedModule.{u, v} A) (k : ℤ)
    (f : shiftComp A k ⟶ (⟨M⟩ : Comp R (DifferentialGradedModule.{u, v} A))) :
    cycleEvaluation A M k f = cycleOfHom A M k f := sorry

/-- Evaluation followed by the cycles inclusion is literal evaluation on the shifted unit. -/
@[simp]
theorem cycleEvaluation_iCycles (A : CochainDGAlgebra.{u, v} R)
    (M : DifferentialGradedModule.{u, v} A) (k : ℤ)
    (f : shiftComp A k ⟶ (⟨M⟩ : Comp R (DifferentialGradedModule.{u, v} A))) :
    ModuleCat.Hom.hom (M.iCycles (-k)) (cycleEvaluation A M k f) =
      cast (congrArg (fun n : ℤ ↦ (M.X n : Type v)) (add_zero (-k)))
        (f.val.1 (-k) (shiftedUnit A k)) := sorry

/-- Evaluation on the shifted unit is natural under postcomposition in the target DG module. -/
theorem cycleEvaluation_naturality (A : CochainDGAlgebra.{u, v} R)
    {M N : DifferentialGradedModule.{u, v} A} (k : ℤ) (g : M ⟶ N)
    (f : shiftComp A k ⟶ (⟨M⟩ : Comp R (DifferentialGradedModule.{u, v} A))) :
    cycleEvaluation A N k (f ≫ (DifferentialGradedModule.toComp A).map g) =
      ModuleCat.Hom.hom ((DifferentialGradedModule.cyclesFunctor A (-k)).map g)
        (cycleEvaluation A M k f) := sorry

/-- The degree equality used to let a cycle generate a degree-zero map from a shifted regular
module. -/
theorem cycleActionIndex (k n : ℤ) : (-k : ℤ) + (n + k) = n + 0 := sorry

/-- The underlying element of the degree-`-k` module represented by a cycle. -/
def cycleValue {A : CochainDGAlgebra.{u, v} R} (M : DifferentialGradedModule.{u, v} A)
    (k : ℤ) (z : M.cycles (-k)) :
    M.X (-k) :=
  ModuleCat.Hom.hom (M.iCycles (-k)) z

/-- A cycle generates a closed degree-zero map from the shifted regular module. -/
def homOfCycle (A : CochainDGAlgebra.{u, v} R) (M : DifferentialGradedModule.{u, v} A)
    (k : ℤ) (z : M.cycles (-k)) :
    shiftComp A k ⟶ (⟨M⟩ : Comp R (DifferentialGradedModule.{u, v} A)) :=
  ⟨⟨fun n ↦
      ModuleCat.castLinearMap
        (congrArg M.X ((neg_add_cancel_comm_assoc k n).trans (add_zero n).symm))
        (M.smul (-k) (n + k) (cycleValue M k z)),
      sorry⟩,
    sorry⟩

/-- Lemma 22.16.2 (1) (09K1): closed maps from the shifted regular module are canonically
`R`-linearly equivalent to the cycles in degree `-k`. -/
@[stacks 09K1 "closed maps from a shifted free module are cycles"]
noncomputable def homLinearEquivCycles (A : CochainDGAlgebra.{u, v} R)
    (M : DifferentialGradedModule.{u, v} A) (k : ℤ) :
    (shiftComp A k ⟶ (⟨M⟩ : Comp R (DifferentialGradedModule.{u, v} A))) ≃ₗ[R]
      M.cycles (-k) where
  toLinearMap := cycleEvaluation A M k
  invFun := homOfCycle A M k
  left_inv := sorry
  right_inv := sorry

/-- The forward map of `homLinearEquivCycles` is evaluation on the shifted unit. -/
@[simp]
theorem homLinearEquivCycles_apply (A : CochainDGAlgebra.{u, v} R)
    (M : DifferentialGradedModule.{u, v} A) (k : ℤ)
    (f : shiftComp A k ⟶ (⟨M⟩ : Comp R (DifferentialGradedModule.{u, v} A))) :
    homLinearEquivCycles A M k f = cycleEvaluation A M k f := sorry

/-- The inverse linear equivalence is the closed map generated by a cycle. -/
@[simp]
theorem homLinearEquivCycles_symm_apply (A : CochainDGAlgebra.{u, v} R)
    (M : DifferentialGradedModule.{u, v} A) (k : ℤ) (z : M.cycles (-k)) :
    (homLinearEquivCycles A M k).symm z = homOfCycle A M k z := sorry

/-- The underlying set equivalence of `homLinearEquivCycles`. -/
noncomputable def homEquivCycles (A : CochainDGAlgebra.{u, v} R)
    (M : DifferentialGradedModule.{u, v} A) (k : ℤ) :
    (shiftComp A k ⟶ (⟨M⟩ : Comp R (DifferentialGradedModule.{u, v} A))) ≃
      M.cycles (-k) :=
  (homLinearEquivCycles A M k).toEquiv

/-- The underlying cycles equivalence evaluates a closed map on the shifted unit. -/
@[simp]
theorem homEquivCycles_apply (A : CochainDGAlgebra.{u, v} R)
    (M : DifferentialGradedModule.{u, v} A) (k : ℤ)
    (f : shiftComp A k ⟶ (⟨M⟩ : Comp R (DifferentialGradedModule.{u, v} A))) :
    homEquivCycles A M k f = cycleOfHom A M k f := sorry

/-- The inverse underlying cycles equivalence is the map generated by the chosen cycle. -/
@[simp]
theorem homEquivCycles_symm_apply (A : CochainDGAlgebra.{u, v} R)
    (M : DifferentialGradedModule.{u, v} A) (k : ℤ) (z : M.cycles (-k)) :
    (homEquivCycles A M k).symm z = homOfCycle A M k z := sorry

/-- Evaluation on the shifted unit followed by the homology projection, as an `R`-linear map
on homotopy classes. -/
noncomputable def homologyEvaluation (A : CochainDGAlgebra.{u, v} R)
    (M : DifferentialGradedModule.{u, v} A) (k : ℤ) :
    (shiftK A k ⟶ (⟨M⟩ : K R (DifferentialGradedModule.{u, v} A))) →ₗ[R]
      M.homology (-k) where
  toFun := Quotient.lift
    (fun f ↦ ModuleCat.Hom.hom (M.homologyπ (-k)) (cycleEvaluation A M k f)) sorry
  map_add' := sorry
  map_smul' := sorry

/-- The compatibility function underlying `homologyEvaluation`. -/
noncomputable abbrev homotopyToHomology (A : CochainDGAlgebra.{u, v} R)
    (M : DifferentialGradedModule.{u, v} A) (k : ℤ) :
    (shiftK A k ⟶ (⟨M⟩ : K R (DifferentialGradedModule.{u, v} A))) →
      M.homology (-k) :=
  homologyEvaluation A M k

/-- On a represented closed map, `homotopyToHomology` is its cycle followed by the homology
projection. -/
theorem homotopyToHomology_inK (A : CochainDGAlgebra.{u, v} R)
    (M : DifferentialGradedModule.{u, v} A) (k : ℤ)
    (f : shiftComp A k ⟶ (⟨M⟩ : Comp R (DifferentialGradedModule.{u, v} A))) :
    homotopyToHomology A M k f.inK =
      ModuleCat.Hom.hom (M.homologyπ (-k)) (cycleOfHom A M k f) := sorry

/-- On a represented closed map, linear homology evaluation is the class of its evaluated
cycle. -/
@[simp]
theorem homologyEvaluation_inK (A : CochainDGAlgebra.{u, v} R)
    (M : DifferentialGradedModule.{u, v} A) (k : ℤ)
    (f : shiftComp A k ⟶ (⟨M⟩ : Comp R (DifferentialGradedModule.{u, v} A))) :
    homologyEvaluation A M k f.inK =
      ModuleCat.Hom.hom (M.homologyπ (-k)) (cycleEvaluation A M k f) := sorry

/-- Evaluation on homotopy classes is natural under postcomposition in the target DG module. -/
theorem homologyEvaluation_naturality (A : CochainDGAlgebra.{u, v} R)
    {M N : DifferentialGradedModule.{u, v} A} (k : ℤ) (g : M ⟶ N)
    (f : shiftK A k ⟶ (⟨M⟩ : K R (DifferentialGradedModule.{u, v} A))) :
    homologyEvaluation A N k (f ≫ (DifferentialGradedModule.toK A).map g) =
      ModuleCat.Hom.hom ((DifferentialGradedModule.homologyFunctor A (-k)).map g)
        (homologyEvaluation A M k f) := sorry

/-- Choose a cycle representative through ModuleCat's explicit kernel-quotient homology model. -/
noncomputable def cycleOfHomology {A : CochainDGAlgebra.{u, v} R}
    (M : DifferentialGradedModule.{u, v} A) (k : ℤ)
    (x : M.homology (-k)) : M.cycles (-k) :=
  (M.toCochainComplex.sc (-k)).moduleCatCyclesIso.inv
    (Quotient.out
      (((M.toCochainComplex.sc (-k)).moduleCatHomologyIso.hom x)))

/-- The chosen cycle representative projects to the original homology class. -/
@[simp]
theorem cycleOfHomology_homologyπ {A : CochainDGAlgebra.{u, v} R}
    (M : DifferentialGradedModule.{u, v} A) (k : ℤ)
    (x : M.homology (-k)) :
    ModuleCat.Hom.hom (M.homologyπ (-k)) (cycleOfHomology M k x) = x := sorry

/-- A homology class determines the homotopy class generated by a chosen cycle representative. -/
noncomputable def homotopyOfHomology (A : CochainDGAlgebra.{u, v} R)
    (M : DifferentialGradedModule.{u, v} A) (k : ℤ) (x : M.homology (-k)) :
    shiftK A k ⟶ (⟨M⟩ : K R (DifferentialGradedModule.{u, v} A)) :=
  (homOfCycle A M k (cycleOfHomology M k x)).inK

/-- Lemma 22.16.2 (2) (09K1): morphisms in the homotopy category from the shifted regular
module are canonically `R`-linearly equivalent to the homology classes in degree `-k`. -/
@[stacks 09K1 "homotopy classes from a shifted free module are homology classes"]
noncomputable def homotopyLinearEquivHomology (A : CochainDGAlgebra.{u, v} R)
    (M : DifferentialGradedModule.{u, v} A) (k : ℤ) :
    (shiftK A k ⟶ (⟨M⟩ : K R (DifferentialGradedModule.{u, v} A))) ≃ₗ[R]
      M.homology (-k) where
  toLinearMap := homologyEvaluation A M k
  invFun := homotopyOfHomology A M k
  left_inv := sorry
  right_inv := sorry

/-- The forward map of `homotopyLinearEquivHomology` is evaluation on the shifted unit. -/
@[simp]
theorem homotopyLinearEquivHomology_apply (A : CochainDGAlgebra.{u, v} R)
    (M : DifferentialGradedModule.{u, v} A) (k : ℤ)
    (f : shiftK A k ⟶ (⟨M⟩ : K R (DifferentialGradedModule.{u, v} A))) :
    homotopyLinearEquivHomology A M k f = homologyEvaluation A M k f := sorry

/-- The inverse linear equivalence is represented by a chosen cycle. -/
@[simp]
theorem homotopyLinearEquivHomology_symm_apply (A : CochainDGAlgebra.{u, v} R)
    (M : DifferentialGradedModule.{u, v} A) (k : ℤ) (x : M.homology (-k)) :
    (homotopyLinearEquivHomology A M k).symm x = homotopyOfHomology A M k x := sorry

/-- The underlying set equivalence of `homotopyLinearEquivHomology`. -/
noncomputable def homotopyEquivHomology (A : CochainDGAlgebra.{u, v} R)
    (M : DifferentialGradedModule.{u, v} A) (k : ℤ) :
    (shiftK A k ⟶ (⟨M⟩ : K R (DifferentialGradedModule.{u, v} A))) ≃
      M.homology (-k) :=
  (homotopyLinearEquivHomology A M k).toEquiv

/-- The underlying homotopy-to-homology equivalence is the canonical evaluation map. -/
@[simp]
theorem homotopyEquivHomology_apply (A : CochainDGAlgebra.{u, v} R)
    (M : DifferentialGradedModule.{u, v} A) (k : ℤ)
    (f : shiftK A k ⟶ (⟨M⟩ : K R (DifferentialGradedModule.{u, v} A))) :
    homotopyEquivHomology A M k f = homotopyToHomology A M k f := sorry

/-- The inverse underlying equivalence is represented by a chosen cycle. -/
@[simp]
theorem homotopyEquivHomology_symm_apply (A : CochainDGAlgebra.{u, v} R)
    (M : DifferentialGradedModule.{u, v} A) (k : ℤ) (x : M.homology (-k)) :
    (homotopyEquivHomology A M k).symm x = homotopyOfHomology A M k x := sorry

end RegularModule

end CochainDGAlgebra
