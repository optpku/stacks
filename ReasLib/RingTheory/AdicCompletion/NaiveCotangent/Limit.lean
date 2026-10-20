module

public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Definition
public import ReasLib.CategoryTheory.Pro.Sequential.Isomorphism
public import ReasLib.RingTheory.AdicCompletion.TopologicallyFiniteType
public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent.Derived
public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent.InverseSystem

/-!
# Limits of adic naive cotangent complexes

The completed naive cotangent complex of a complete topologically finite type algebra is strictly
pro-isomorphic, in `D(B)`, to the inverse system of stage naive cotangent
complexes, and is a homotopy limit of that system.
-/

@[expose] public section

open Algebra.NaiveCotangent.Adic
open CategoryTheory

universe u

namespace Algebra.NaiveCotangent.Adic

variable {A B ι : Type u} [CommRing A] [noetherian : IsNoetherianRing A] [CommRing B] [Algebra A B] [Fintype ι]
variable (I : Ideal A) [finiteType : Algebra.TopologicallyFiniteType I B]
variable (P : Presentation A B I ι)

include noetherian finiteType

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

/-- The canonical derived comparison admits an inverse after one constant shift. -/
theorem modToStageDerivedNatTrans_hasShiftInverse :
    ∃ (c : ℕ) (β : (stageDerivedSystem I P).shift c ⟶ modDerivedSystem I P),
      Pro.SequentialHom.IsShiftInverse (modToStageDerivedNatTrans I P) c β :=
  sorry

/-- The derived comparison is invertible as a sequential pro-morphism. -/
theorem modDerivedSystem_hasRepresentativeInverse :
    (modToStageDerivedHom I P).HasRepresentativeInverse :=
  sorry

/-- The completed naive cotangent object is a homotopy limit of the stage-derived tower. -/
theorem naiveCotangentObject_isHomotopyLimit :
    HomotopyLimit.IsOf (stageDerivedSystem I P) (naiveCotangentObject I P) :=
  sorry

end Algebra.NaiveCotangent.Adic
