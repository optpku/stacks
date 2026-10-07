module

public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Definition
public import ReasLib.CategoryTheory.Pro.Sequential.Isomorphism
public import stacks_project.Chap88.«88_2_0_2_TopologicallyFiniteType»
public import stacks_project.Chap88.Definition_88_8_1_Derived
public import stacks_project.Chap88.Lemma_88_3_3_System

/-!
# Lemma 88.3.3

The completed naive cotangent complex of an object of (88.2.0.2) is strictly
pro-isomorphic, in `D(B)`, to the inverse system of stage naive cotangent
complexes, and is a homotopy limit of that system.
-/

@[expose] public section

open Algebra.NaiveCotangent.Adic
open CategoryTheory

universe u

namespace Algebra.NaiveCotangent.Adic

variable {A B ι : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B] [Fintype ι]
variable (I : Ideal A) [Algebra.TopologicallyFiniteType I B]
variable (P : Presentation A B I ι)

/-- There is a constant Artin–Rees shift making the complex-level comparison
`modToStageNatTrans` inverse, up to transition maps, to a reverse family of
maps of complexes. -/
theorem exists_isShiftInverse :
    ∃ (c : ℕ) (β : (stageSystem I P).shift c ⟶ modSystem I P),
      Pro.SequentialHom.IsShiftInverse (modToStageNatTrans I P) c β :=
  sorry

/-- The completed naive cotangent object is a homotopy limit of the inverse
system `{NL_{B/A}^∧ ⊗_B B / I^{n+1} B}` in `D(B)`. -/
theorem naiveCotangentObject_isHomotopyLimit_mod :
    HomotopyLimit.IsOf (modDerivedSystem I P) (naiveCotangentObject I P) :=
  sorry

/-- Lemma 88.3.3 (1): Let `A` be a Noetherian ring and let `I ⊂ A` be an ideal.
Let `B` be an object of (88.2.0.2). Then the pro-objects
`{NL_{B/A}^∧ ⊗_B B / I^n B}` and `{NL_{B_n/A_n}}` of `D(B)` are strictly
isomorphic, where `A_n` and `B_n` are as in Section 88.2. -/
@[stacks 0AJS]
theorem modToStageDerivedNatTrans_hasShiftInverse :
    ∃ (c : ℕ) (β : (stageDerivedSystem I P).shift c ⟶ modDerivedSystem I P),
      Pro.SequentialHom.IsShiftInverse (modToStageDerivedNatTrans I P) c β :=
  sorry

/-- The derived comparison is invertible as a sequential pro-morphism. -/
theorem modDerivedSystem_hasRepresentativeInverse :
    (modToStageDerivedHom I P).HasRepresentativeInverse :=
  sorry

/-- Lemma 88.3.3 (2): Let `A` be a Noetherian ring and let `I ⊂ A` be an ideal.
Let `B` be an object of (88.2.0.2). Then `NL_{B/A}^∧` is a homotopy limit of
`{NL_{B_n/A_n}}` in `D(B)`, where `A_n` and `B_n` are as in Section 88.2. -/
@[stacks 0AJS]
theorem naiveCotangentObject_isHomotopyLimit :
    HomotopyLimit.IsOf (stageDerivedSystem I P) (naiveCotangentObject I P) :=
  sorry

end Algebra.NaiveCotangent.Adic
