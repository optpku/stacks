/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Local isomorphism of sheaves

Sheaves are locally isomorphic when each slice site is covered by objects on
which their restrictions are isomorphic.
-/

@[expose] public section

open CategoryTheory

universe u v w w'

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {D : Type w} [Category.{w'} D]
variable [HasWeakSheafify J D]
variable [∀ U : C, HasWeakSheafify (J.over U) D]

/-- A pair of sheaves is locally isomorphic when every slice site admits a covering by
objects on which the restrictions are isomorphic. -/
class IsLocallyIsomorphic (F G : Sheaf J D) : Prop where
  /-- Every object admits a covering by local isomorphisms of restrictions. -/
  existsCover (U : C) :
    ∃ (ι : Type (max u v)) (X : ι → Over U), (J.over U).CoversTop X ∧
      ∀ i : ι, Nonempty ((F.over (X i).left) ≅ (G.over (X i).left))

/-- Local isomorphism is reflexive. -/
instance instIsLocallyIsomorphic_self (F : Sheaf J D) : IsLocallyIsomorphic F F :=
  sorry

/-- Unfolding `IsLocallyIsomorphic` recovers the covering-by-isos criterion. -/
theorem isLocallyIsomorphic_iff (F G : Sheaf J D) :
    IsLocallyIsomorphic F G ↔
      ∀ U : C,
        ∃ (ι : Type (max u v)) (X : ι → Over U), (J.over U).CoversTop X ∧
          ∀ i : ι, Nonempty ((F.over (X i).left) ≅ (G.over (X i).left)) :=
  sorry

/-- Local isomorphism is symmetric. -/
theorem isLocallyIsomorphic_symm {F G : Sheaf J D} [IsLocallyIsomorphic F G] :
    IsLocallyIsomorphic G F :=
  sorry

/-- Local isomorphism is invariant under replacing either sheaf by an isomorphic sheaf. -/
theorem isLocallyIsomorphic_of_iso {F G H : Sheaf J D} (e : F ≅ G)
    [IsLocallyIsomorphic F H] : IsLocallyIsomorphic G H :=
  sorry

end CategoryTheory.Sheaf
