/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.ChainComplex.Monoidal.Symmetric
public import ReasLib.Algebra.Homology.HomologicalComplex.Monoidal.Component
public import ReasLib.CategoryTheory.GradedObject.Monoid
public import ReasLib.RingTheory.Sequence.Koszul.Multiplication
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.Tactic.CrossRefAttribute

/-!
# Koszul complexes as commutative monoid objects

@stack 062K

The exterior unit and wedge product assemble into chain maps for the Koszul differential. This
packages the ordinary module-valued Koszul complex as a commutative monoid in nonnegative chain
complexes, with commutativity measured by the Koszul braiding.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory ComplexShape
open CategoryTheory.MonObj

noncomputable section

universe u

namespace KoszulComplex

variable {R E : Type u} [CommRing R] [AddCommGroup E] [Module R E]

/-- The exterior unit assembled into a chain map from the tensor-unit complex. -/
@[stacks 062K "unit chain map of a module-valued Koszul complex"]
noncomputable def oneHom (phi : E →ₗ[R] R) :
    𝟙_ (ChainComplex (ModuleCat R) ℕ) ⟶ koszulComplex phi where
  f n :=
    (HomologicalComplex.tensorUnitIso (ModuleCat R) (down ℕ)).inv n ≫
      GradedObject.Monoidal.oneHom (koszulComplex phi).X
        (ModuleCat.exteriorPower.one (ModuleCat.of R E)) n
  comm' := sorry

/-- Exterior multiplication assembled into a multiplication chain map on a Koszul complex. -/
@[stacks 062K "multiplication chain map of a module-valued Koszul complex"]
noncomputable def mulHom (phi : E →ₗ[R] R) :
    HomologicalComplex.tensorObj (koszulComplex phi) (koszulComplex phi) ⟶
      koszulComplex phi where
  f n := HomologicalComplex.mapBifunctorDesc
    (K₁ := koszulComplex phi) (K₂ := koszulComplex phi)
    (F := curriedTensor (ModuleCat R)) (c := down ℕ)
    fun p q h ↦ ModuleCat.exteriorPower.mul (ModuleCat.of R E) p q ≫
      eqToHom (congrArg (koszulComplex phi).X h)
  comm' := sorry

/-- The assembled Koszul unit is a left identity. -/
theorem oneHom_mulHom (phi : E →ₗ[R] R) :
    oneHom phi ▷ koszulComplex phi ≫ mulHom phi =
      (λ_ (koszulComplex phi)).hom := sorry

/-- The assembled Koszul unit is a right identity. -/
theorem mulHom_oneHom (phi : E →ₗ[R] R) :
    koszulComplex phi ◁ oneHom phi ≫ mulHom phi =
      (ρ_ (koszulComplex phi)).hom := sorry

/-- The assembled exterior multiplication on a Koszul complex is associative. -/
theorem mulHom_assoc (phi : E →ₗ[R] R) :
    (mulHom phi ▷ koszulComplex phi) ≫ mulHom phi =
      (α_ (koszulComplex phi) (koszulComplex phi) (koszulComplex phi)).hom ≫
        (koszulComplex phi ◁ mulHom phi) ≫ mulHom phi := sorry

/-- Exterior multiplication is commutative for the Koszul braiding on chain complexes. -/
theorem mulHom_comm (phi : E →ₗ[R] R) :
    (β_ (koszulComplex phi) (koszulComplex phi)).hom ≫ mulHom phi =
      mulHom phi := sorry

/-- The canonical monoid-object structure on a module-valued Koszul chain complex. -/
@[stacks 062K "monoid-object structure on a module-valued Koszul complex",
  stacks 0GZJ "monoid-object structure on powered Koszul complexes", implicit_reducible]
noncomputable instance monObj (phi : E →ₗ[R] R) : MonObj (koszulComplex phi) where
  one := oneHom phi
  mul := mulHom phi
  one_mul := oneHom_mulHom phi
  mul_one := mulHom_oneHom phi
  mul_assoc := mulHom_assoc phi

/-- A module-valued Koszul chain complex is commutative for the Koszul braiding. -/
@[stacks 062K "commutativity of a module-valued Koszul complex"]
noncomputable instance isCommMonObj (phi : E →ₗ[R] R) :
    IsCommMonObj (koszulComplex phi) where
  mul_comm := mulHom_comm phi

/-- Definition 15.28.1 (1) and Definition 17.24.1 (062K): the module-valued Koszul complex,
bundled as a commutative differential graded algebra in nonnegative chain complexes. -/
@[stacks 0622 "(1), exterior Koszul differential graded algebra",
  stacks 062K "module-valued Koszul commutative differential graded algebra",
  stacks 0GZJ "powered Koszul commutative differential graded algebra", implicit_reducible]
noncomputable def commMon (phi : E →ₗ[R] R) :
    CommMon (ChainComplex (ModuleCat R) ℕ) where
  X := koszulComplex phi
  mon := monObj phi
  comm := isCommMonObj phi

/-- The underlying chain complex of the bundled Koszul algebra is its Koszul complex. -/
@[simp]
theorem commMon_X (phi : E →ₗ[R] R) :
    (commMon phi).X = koszulComplex phi := sorry

/-- The unit of the bundled Koszul algebra is the assembled exterior unit. -/
@[simp]
theorem commMon_one (phi : E →ₗ[R] R) :
    η[(commMon phi).X] = oneHom phi := sorry

/-- The multiplication of the bundled Koszul algebra is the assembled exterior product. -/
@[simp]
theorem commMon_mul (phi : E →ₗ[R] R) :
    μ[(commMon phi).X] = mulHom phi := sorry

/-- The degree-zero component of the Koszul unit is the exterior unit. -/
@[simp]
theorem oneHom_component (phi : E →ₗ[R] R) :
    HomologicalComplex.Monoidal.unitHomComponent (oneHom phi) =
      ModuleCat.exteriorPower.one (ModuleCat.of R E) := sorry

/-- The `(n, m)` component of Koszul multiplication is exterior multiplication. -/
@[simp]
theorem mulHom_component (phi : E →ₗ[R] R) (n m : ℕ) :
    HomologicalComplex.Monoidal.tensorHomComponent (mulHom phi) n m =
      ModuleCat.exteriorPower.mul (ModuleCat.of R E) n m := sorry

end KoszulComplex
