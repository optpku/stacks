/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.Sober
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Reduced
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Irreducible
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Inertia
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Immersion
public import ReasLib.CategoryTheory.Fibered.Groupoids.GerbeMorphism

/-!
# Integral algebraic stacks

An algebraic stack is integral when it is reduced, decent, its inertia
morphism is quasi-compact, and its space of points is irreducible. This is
strictly stronger than reduced and irreducible.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids.Inertia (forget)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- An algebraic stack is integral if it is reduced, decent, the inertia
morphism `I_X ⟶ X` is quasi-compact, and `|X|` is irreducible. -/
@[mk_iff]
class IsIntegral {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    Prop extends IsReduced X, IsDecent X, IsIrreducible X where
  /-- The inertia morphism `I_X ⟶ X` is quasi-compact. -/
  inertia_quasiCompact : QuasiCompact (forget.{u + 1, u, u, u + 1} X)

namespace IsIntegral

/-- An integral algebraic stack is reduced and decent, has quasi-compact
inertia morphism, and is irreducible. -/
theorem spec {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsIntegral X] :
    IsReduced X ∧ IsDecent X ∧ QuasiCompact (forget.{u + 1, u, u, u + 1} X) ∧
      IsIrreducible X :=
  sorry

/-- Reducedness, decency, quasi-compact inertia, and irreducibility together
witness that an algebraic stack is integral. -/
@[instance 900]
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [IsReduced X] [IsDecent X] [IsIrreducible X]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)] : IsIntegral X :=
  sorry

/-- The canonical point space of an integral algebraic stack is sober. -/
theorem sober {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsIntegral X] : T0Space (Points X) ∧ QuasiSober (Points X) :=
  sorry

/-- The canonical point space of an integral algebraic stack has a unique generic point. -/
theorem existsUnique_genericPoint {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsIntegral X] :
    ∃! x : Points X, IsGenericPoint x Set.univ :=
  sorry

/-- An integral algebraic stack contains an open substack that is a gerbe over
an integral scheme. -/
theorem exists_openSubstack_gerbeOver_integralScheme
    {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] [IsIntegral X] :
    ∃ (U : GroupoidsOver S) (ι : U ⟶ X) (V : Over S)
      (π : U ⟶ GroupoidsOver.slice V),
      AlgebraicStack U ∧ AlgebraicGeometry.Groupoids.Hom.OpenImmersion ι ∧
        AlgebraicGeometry.IsIntegral V.left ∧
        CategoryTheory.FiberedCategoryOver.Groupoids.Hom.IsGerbeMorphism
          (Scheme.fppfTopology.over S) π :=
  sorry

end IsIntegral

/-- The canonical slice of an integral scheme over `S` is an integral algebraic
stack. -/
instance instIsIntegral_slice {S : Scheme.{u}} (U : Over S)
    [AlgebraicGeometry.IsIntegral U.left] :
    IsIntegral (GroupoidsOver.slice U) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
