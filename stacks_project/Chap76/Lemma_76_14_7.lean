/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_38_8_Unramified
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap76.Lemma_76_14_6

/-!
# Unramified morphisms of algebraic spaces versus vanishing differentials

A morphism of algebraic spaces is unramified if and only if it is locally of
finite type and either its sheaf of relative differentials vanishes or it is
formally unramified.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits
open scoped AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.14.7 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Then `f` is unramified if and only if `f` is locally
of finite type and the sheaf of relative differentials `Ω[f]` vanishes. -/
@[stacks 04GA]
theorem unramified_iff_locallyOfFiniteType_and_isZero_relativeDifferentials
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Unramified f ↔ LocallyOfFiniteType f ∧ IsZero (Ω[f]) :=
  sorry

/-- Lemma 76.14.7 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Then `f` is unramified if and only if `f` is locally
of finite type and formally unramified. -/
@[stacks 04GA]
theorem unramified_iff_locallyOfFiniteType_and_formallyUnramified
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Unramified f ↔ LocallyOfFiniteType f ∧ FormallyUnramified f :=
  sorry

/-- An unramified morphism of algebraic spaces is formally unramified. -/
instance formallyUnramified_of_unramified {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Unramified f] : FormallyUnramified f :=
  sorry

/-- A morphism of algebraic spaces that is locally of finite type and formally
unramified is unramified. -/
instance unramified_of_locallyOfFiniteType_of_formallyUnramified
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [FormallyUnramified f] : Unramified f :=
  sorry

/-- A morphism of algebraic spaces that is locally of finite type and whose
sheaf of relative differentials vanishes is unramified. -/
theorem unramified_of_locallyOfFiniteType_of_isZero_relativeDifferentials
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (h : IsZero (Ω[f])) : Unramified f :=
  sorry

namespace Unramified

/-- An algebraic-space morphism that is locally of finite type is unramified if
and only if its sheaf of relative differentials vanishes. -/
theorem iff_isZero_relativeDifferentials {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [LocallyOfFiniteType f] : Unramified f ↔ IsZero (Ω[f]) :=
  sorry

/-- An algebraic-space morphism that is locally of finite type is unramified if
and only if it is formally unramified. -/
theorem iff_formallyUnramified {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [LocallyOfFiniteType f] :
    Unramified f ↔ FormallyUnramified f :=
  sorry

end Unramified

end AlgebraicGeometry.AlgebraicSpace
