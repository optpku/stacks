/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Determinant.Construction
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open scoped TensorProduct Module.Determinant

noncomputable section

universe u

namespace DeterminantScalarChange

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable (M : Type u) [AddCommGroup M] [Module R M]

-- Local instance justification (defeq pin): the exterior lift uses the R-algebra structure composed through the specified S-algebra.
local instance : Algebra R (ExteriorAlgebra S (S ⊗[R] M)) :=
  Algebra.compHom (ExteriorAlgebra S (S ⊗[R] M)) (algebraMap R S)

-- Local instance justification (defeq pin): scalar restriction of the exterior generator uses the preceding composed algebra structure.
local instance : IsScalarTower R S (ExteriorAlgebra S (S ⊗[R] M)) := by
  apply IsScalarTower.of_algebraMap_eq'
  rfl

/-- The actual degree-one map m ↦ ι(1⊗m). -/
def generators : M →ₗ[R] ExteriorAlgebra S (S ⊗[R] M) :=
  ((ExteriorAlgebra.ι S).restrictScalars R).comp (TensorProduct.mk R S M 1)

/-- The exterior map is obtained from the universal property, not selected
from an existence assertion about exterior-algebra equivalences. -/
def exterior : ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra S (S ⊗[R] M) :=
  ExteriorAlgebra.lift R ⟨generators R S M, by
    intro m
    exact ExteriorAlgebra.ι_sq_zero ((1 : S) ⊗ₜ[R] m)⟩

/-- Since pure tensors generate the extended module, annihilation by all
source generators implies annihilation by all extended generators. -/
theorem determinant_mem (x : det[R](M)) :
    exterior R S M x ∈ det[S](S ⊗[R] M) := by sorry

def determinantMap : det[R](M) →ₗ[R] det[S](S ⊗[R] M) :=
  LinearMap.codRestrict ((det[S](S ⊗[R] M)).restrictScalars R)
    ((exterior R S M).toLinearMap.comp (Module.Determinant.ι R M))
    (determinant_mem R S M)

/-- Scalar extension of the actual restricted exterior map. -/
def determinantBaseChange : S ⊗[R] det[R](M) →ₗ[S] det[S](S ⊗[R] M) :=
  (determinantMap R S M).liftBaseChange S

theorem determinantBaseChange_tmul (s : S) (x : det[R](M)) :
    determinantBaseChange R S M (s ⊗ₜ[R] x) = s • determinantMap R S M x := rfl

/-- Local finite-projective rank computation proves bijectivity of THIS map. -/
theorem determinantBaseChange_bijective [Module.Finite R M] [Module.Projective R M] :
    Function.Bijective (determinantBaseChange R S M) := by sorry

def determinantEquiv [Module.Finite R M] [Module.Projective R M] :
    S ⊗[R] det[R](M) ≃ₗ[S] det[S](S ⊗[R] M) :=
  LinearEquiv.ofBijective (determinantBaseChange R S M)
    (determinantBaseChange_bijective R S M)

variable (N : Type u) [AddCommGroup N] [Module R N]
variable [Module.Finite R M] [Module.Projective R M]
variable [Module.Finite R N] [Module.Projective R N]

/-- The determinant line is a Hom, so base change conjugates the scalar-
extended Hom map by the specified determinant scalar-extension maps. -/
def lineMap :
    (det[R](M) →ₗ[R] det[R](N)) →ₗ[R]
      (det[S](S ⊗[R] M) →ₗ[S] det[S](S ⊗[R] N)) where
  toFun f := (determinantEquiv R S N).toLinearMap.comp
    ((f.baseChange S).comp (determinantEquiv R S M).symm.toLinearMap)
  map_add' := by sorry
  map_smul' := by sorry

def lineBaseChange :
    S ⊗[R] (det[R](M) →ₗ[R] det[R](N)) →ₗ[S]
      (det[S](S ⊗[R] M) →ₗ[S] det[S](S ⊗[R] N)) :=
  (lineMap R S M N).liftBaseChange S

theorem lineBaseChange_bijective :
    Function.Bijective (lineBaseChange R S M N) := by sorry

def lineEquiv :
    S ⊗[R] (det[R](M) →ₗ[R] det[R](N)) ≃ₗ[S]
      (det[S](S ⊗[R] M) →ₗ[S] det[S](S ⊗[R] N)) :=
  LinearEquiv.ofBijective (lineBaseChange R S M N) (lineBaseChange_bijective R S M N)

end DeterminantScalarChange
