/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommCompactModule
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CompactCharacters

@[expose] public section
open CategoryTheory Opposite
noncomputable section
universe u

namespace NoncommCompactCharacters
variable (R : Type u) [Ring R] [Finite R]
variable (M : ModuleCat.{u} R)

/-- Finite-ring additive order annihilates any left module; commutativity is unnecessary. -/
theorem annihilated (m : M) : Nat.card R • m = 0 := by sorry

/-- Actual finite-valued evaluation coordinates for a right character. -/
def coordinates (χ : ActualOppositeCharacter.Carrier M) : M → CompactCharacters.Roots (Nat.card R) :=
  fun m ↦ ⟨χ m, by
    change Nat.card R • (show CharacterModule M from χ) m = 0
    rw [← map_nsmul, annihilated R M, map_zero]⟩

/-- The right character module with pointwise convergence in finite annihilators. -/
def dual : NoncommCompactModule Rᵐᵒᵖ where
  toModule := ModuleCat.of Rᵐᵒᵖ (ActualOppositeCharacter.Carrier M)
  topology := TopologicalSpace.induced (coordinates R M) inferInstance
  compact := by sorry
  t2 := by sorry
  topologicalAdd := by sorry
  scalarContinuous := by sorry

/-- Precomposition is continuous in the actual finite-coordinate topology. -/
theorem map_continuous {N : ModuleCat.{u} R} (f : M ⟶ N) :
    Continuous (show (dual R N).toModule → (dual R M).toModule from
      ActualOppositeCharacter.map R M f.hom) := by sorry

/-- Continuous right-linear character precomposition. -/
def map {N : ModuleCat.{u} R} (f : M ⟶ N) : dual R N ⟶ dual R M :=
  { toLinearMap := ActualOppositeCharacter.map R M f.hom
    cont := map_continuous R M f }

/-- The actual contravariant compact character functor changes R to Rᵐᵒᵖ. -/
def functor : (ModuleCat.{u} R)ᵒᵖ ⥤ NoncommCompactModule Rᵐᵒᵖ where
  obj M := dual R M.unop
  map f := map R _ f.unop
  map_id := by intros; rfl
  map_comp := by intros; rfl

end NoncommCompactCharacters
