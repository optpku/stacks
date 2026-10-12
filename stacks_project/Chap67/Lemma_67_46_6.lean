/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Definition_67_46_2_FiniteLocallyFree
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat

/-!
# Finite locally free morphisms of algebraic spaces versus finite, flat, and
locally of finite presentation

A morphism of algebraic spaces is finite locally free if and only if it is
finite, flat, and locally of finite presentation. Over a locally Noetherian
target, finite plus flat is equivalent.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace FiniteLocallyFree

/-- Lemma 67.46.6 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Then `f` is finite locally free if and only if `f`
is finite, flat, and locally of finite presentation. -/
@[stacks 0416]
theorem iff_isFinite_and_flat_and_locallyOfFinitePresentation
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    FiniteLocallyFree f ↔ IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f :=
  sorry

/-- Lemma 67.46.6 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. If `Y` is locally Noetherian, then `f` is finite
locally free if and only if `f` is finite and flat. -/
@[stacks 0416]
theorem iff_isFinite_and_flat {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsLocallyNoetherian Y] :
    FiniteLocallyFree f ↔ IsFinite f ∧ Flat f :=
  sorry

/-- A finite locally free morphism of algebraic spaces is finite. -/
instance instIsFinite {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [FiniteLocallyFree f] : IsFinite f :=
  sorry

/-- A finite locally free morphism of algebraic spaces is flat. -/
instance instFlat {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [FiniteLocallyFree f] : Flat f :=
  sorry

/-- A finite locally free morphism of algebraic spaces is locally of finite
presentation. -/
instance instLocallyOfFinitePresentation {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [FiniteLocallyFree f] :
    LocallyOfFinitePresentation f :=
  sorry

/-- A finite, flat, and locally of finite presentation morphism of algebraic
spaces is finite locally free. -/
instance of_isFinite_of_flat_of_locallyOfFinitePresentation {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f] : FiniteLocallyFree f :=
  sorry

/-- Over a locally Noetherian target, a finite and flat morphism of algebraic
spaces is finite locally free. -/
instance of_isFinite_of_flat {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsLocallyNoetherian Y] [IsFinite f] [Flat f] :
    FiniteLocallyFree f :=
  sorry

end FiniteLocallyFree

end AlgebraicGeometry.AlgebraicSpace
