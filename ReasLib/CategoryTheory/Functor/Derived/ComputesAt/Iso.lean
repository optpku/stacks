/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt
public import ReasLib.CategoryTheory.Functor.Derived.Definedness.Domain
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Isomorphism Closure for Computing Pointwise Derived Values

The pointwise condition that an object already computes a derived value is invariant under
isomorphism.  This leaf records the object-property instances and direct transport lemmas without
assuming a shift or triangulated structure.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open ObjectProperty

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  (F : D ⥤ D') (S : MorphismProperty D)
  [S.ContainsIdentities]

/-- Stacks 05SX: the objects computing the pointwise right-derived value of `F` are closed
under isomorphisms. -/
@[stacks 05SX]
instance Functor.RightDerived.ComputesAt.closedUnderIso :
    IsClosedUnderIsomorphisms (Functor.RightDerived.ComputesAt.objects F S) := sorry

/-- Stacks 05SX: the objects computing the pointwise left-derived value of `F` are closed
under isomorphisms. -/
@[stacks 05SX]
instance Functor.LeftDerived.ComputesAt.closedUnderIso :
    IsClosedUnderIsomorphisms (Functor.LeftDerived.ComputesAt.objects F S) := sorry

/-- A right-derived computation condition transports along a source isomorphism. -/
@[stacks 05SX]
theorem Functor.RightDerived.ComputesAt.of_iso {X Y : D} (e : X ≅ Y)
    (hX : Functor.RightDerived.ComputesAt F S X) :
    Functor.RightDerived.ComputesAt F S Y :=
  (Functor.RightDerived.ComputesAt.objects F S).prop_of_iso e hX

/-- A left-derived computation condition transports along a source isomorphism. -/
@[stacks 05SX]
theorem Functor.LeftDerived.ComputesAt.of_iso {X Y : D} (e : X ≅ Y)
    (hX : Functor.LeftDerived.ComputesAt F S X) :
    Functor.LeftDerived.ComputesAt F S Y :=
  (Functor.LeftDerived.ComputesAt.objects F S).prop_of_iso e hX

end CategoryTheory
