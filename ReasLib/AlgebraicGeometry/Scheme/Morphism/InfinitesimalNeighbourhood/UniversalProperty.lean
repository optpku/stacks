/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Factorization
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.InfinitesimalNeighbourhood

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom.InfinitesimalNeighbourhood

/-- A commutative square over an immersion induces a commutative square against the
canonical map from its `n`th infinitesimal neighbourhood to the ambient scheme. -/
theorem factorizationCommSq {Z X T T' : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (n : ℕ) (j : T ⟶ T') (a : T ⟶ Z) (b : T' ⟶ X) (sq : CommSq a j i b) :
    CommSq (a ≫ fromSource i n) j (toAmbient i n) b := sorry

/-- For `1 ≤ n`, every `n`th-order thickening in a commutative square over an immersion
admits a unique lift to the canonical `n`th infinitesimal neighbourhood. -/
theorem existsUnique_lift {Z X T T' : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (n : ℕ) (hn : 1 ≤ n) (j : T ⟶ T') [IsNthOrderThickening n j]
    (a : T ⟶ Z) (b : T' ⟶ X) (sq : CommSq a j i b) :
    Nonempty (Unique (factorizationCommSq i n j a b sq).LiftStruct) := sorry

/-- Every first-order thickening in a commutative square over an immersion admits a unique
lift to the canonical first-order infinitesimal neighbourhood. -/
theorem existsUnique_lift_firstOrder {Z X T T' : Scheme.{u}}
    (i : Z ⟶ X) [IsImmersion i] (j : T ⟶ T') [IsFirstOrderThickening j]
    (a : T ⟶ Z) (b : T' ⟶ X) (sq : CommSq a j i b) :
    Nonempty (Unique (factorizationCommSq i 1 j a b sq).LiftStruct) := sorry

end AlgebraicGeometry.Scheme.Hom.InfinitesimalNeighbourhood
