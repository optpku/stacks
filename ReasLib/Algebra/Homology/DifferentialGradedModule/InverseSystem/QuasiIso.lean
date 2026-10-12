/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.QuasiIso
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Forget
public import ReasLib.Algebra.Homology.DifferentialGradedModule.InverseSystem
import Mathlib.Tactic.CrossRefAttribute

/-!
# Quasi-isomorphisms of differential graded module systems

The weak equivalences of DG-module systems are the morphisms which are quasi-isomorphisms on the
underlying cochain complex at every stage.  This property is localized globally, after the
transition data has been assembled into one object.
-/

@[expose] public section

noncomputable section

universe u x v

open CategoryTheory

namespace DifferentialGradedModule.InverseSystem

variable {R : Type u} [CommRing R]

/-- A morphism of DG-module systems is a quasi-isomorphism when it is one at every stage. -/
@[stacks 0GZG "levelwise quasi-isomorphisms of DG-module systems"]
def quasiIso (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)) :
    MorphismProperty (System.{u, x, v} A) :=
  fun _ _ f ↦ ∀ n : ℕ, _root_.QuasiIso (f.app n).toCochainMap

namespace QuasiIso

variable {A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)}

/-- A system morphism is a quasi-isomorphism exactly when every stage map is one. -/
theorem iff {M N : System A} (f : M ⟶ N) :
    quasiIso A f ↔ ∀ n : ℕ, _root_.QuasiIso (f.app n).toCochainMap := sorry

/-- Levelwise quasi-isomorphisms contain identity morphisms. -/
instance containsIdentities : (quasiIso A).ContainsIdentities := sorry

/-- Levelwise quasi-isomorphisms are closed under composition. -/
instance isMultiplicative : (quasiIso A).IsMultiplicative := sorry

/-- Levelwise quasi-isomorphisms satisfy two-out-of-three. -/
instance hasTwoOutOfThree : (quasiIso A).HasTwoOutOfThreeProperty := sorry

/-- Levelwise quasi-isomorphisms are stable under retracts. -/
instance isStableUnderRetracts : (quasiIso A).IsStableUnderRetracts := sorry

end QuasiIso

end DifferentialGradedModule.InverseSystem
