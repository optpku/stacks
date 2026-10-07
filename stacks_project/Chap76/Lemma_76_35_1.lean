module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Lemma_67_27_5_DiscreteFiber
public import stacks_project.Chap67.Lemma_67_27_7_LocallyQuasiFinite

/-!
# Characterizations of finite morphisms of algebraic spaces

A morphism of algebraic spaces is finite if and only if it is proper and
locally quasi-finite, equivalently proper with discrete field fibers, equivalently
universally closed, separated, and locally of finite type with discrete field
fibers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsFinite

/-- Lemma 76.35.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. The following are equivalent: `f` is finite; `f` is
proper and locally quasi-finite; `f` is proper and every field fiber
`Points (pullback f g)` is discrete; `f` is universally closed, separated, and
locally of finite type, and every field fiber is discrete.

The field-fiber condition is `discreteFieldFibers f`. -/
@[stacks 0A4X]
theorem proper_discreteFieldFibers_tfae {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    List.TFAE
      [ IsFinite f
      , Proper f ∧ LocallyQuasiFinite f
      , Proper f ∧ discreteFieldFibers f
      , UniversallyClosed f ∧ Separated f ∧ LocallyOfFiniteType f ∧
          discreteFieldFibers f ] :=
  sorry

/-- A morphism of algebraic spaces is finite if and only if it is proper and
locally quasi-finite. -/
theorem iff_proper_and_locallyQuasiFinite {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    IsFinite f ↔ Proper f ∧ LocallyQuasiFinite f :=
  sorry

/-- A morphism of algebraic spaces is finite if and only if it is proper and
has discrete field fibers. -/
theorem iff_proper_and_discreteFieldFibers {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    IsFinite f ↔ Proper f ∧ discreteFieldFibers f :=
  sorry

/-- A proper and locally quasi-finite morphism of algebraic spaces is finite. -/
theorem of_proper_of_locallyQuasiFinite {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f] [LocallyQuasiFinite f] :
    IsFinite f :=
  sorry

end IsFinite

end AlgebraicGeometry.AlgebraicSpace
