/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.AbsoluteTransformations.Maps.Construction
public import stacks_project.Chap101.Definition_101_4_2_Separation
public import stacks_project.Chap101.Lemma_101_19_1_AutomorphismGroup

/-!
# Scheme-ness of automorphism groups of field-valued points

The automorphism group algebraic space of a field-valued point of an algebraic
stack is a scheme whenever the object diagonal or the inertia morphism
satisfies a listed separation or quasi-finiteness hypothesis, or the stack is
quasi-DM.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open FiberedCategoryOver.Groupoids.Inertia
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace automorphismGroup

namespace IsScheme

/-- Lemma 101.19.1 (1): If the object diagonal `diagonal X : X ⟶ X ×_S X` is
quasi-separated, then the automorphism group algebraic space of a field-valued
point is a scheme. -/
@[stacks 0DTS]
theorem of_quasiSeparated_diagonal {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (p : FieldValuedPoint X)
    (h : Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
      (diagonal.{u + 1, u, u + 1} X)) :
    IsScheme p :=
  sorry

/-- Lemma 101.19.1 (2): If the object diagonal `diagonal X : X ⟶ X ×_S X` is
locally separated, then the automorphism group algebraic space of a field-valued
point is a scheme. -/
@[stacks 0DTS]
theorem of_locallySeparated_diagonal {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (p : FieldValuedPoint X)
    (h : Groupoids.Hom.has (@AlgebraicSpace.LocallySeparated S)
      (diagonal.{u + 1, u, u + 1} X)) :
    IsScheme p :=
  sorry

/-- Lemma 101.19.1 (3): If `X` is quasi-DM, then the automorphism group
algebraic space of a field-valued point is a scheme. -/
@[stacks 0DTS]
theorem of_isQuasiDM {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsQuasiDM X] (p : FieldValuedPoint X) :
    IsScheme p :=
  sorry

/-- Lemma 101.19.1 (4): If the inertia morphism `Inertia.forget X : I_X ⟶ X` is
quasi-separated, then the automorphism group algebraic space of a field-valued
point is a scheme. -/
@[stacks 0DTS]
theorem of_quasiSeparated_inertia {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (p : FieldValuedPoint X)
    (h : Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
      (forget.{u + 1, u, u, u + 1} X)) :
    IsScheme p :=
  sorry

/-- Lemma 101.19.1 (5): If the inertia morphism `Inertia.forget X : I_X ⟶ X` is
locally separated, then the automorphism group algebraic space of a field-valued
point is a scheme. -/
@[stacks 0DTS]
theorem of_locallySeparated_inertia {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (p : FieldValuedPoint X)
    (h : Groupoids.Hom.has (@AlgebraicSpace.LocallySeparated S)
      (forget.{u + 1, u, u, u + 1} X)) :
    IsScheme p :=
  sorry

/-- Lemma 101.19.1 (6): If the inertia morphism `Inertia.forget X : I_X ⟶ X` is
locally quasi-finite, then the automorphism group algebraic space of a
field-valued point is a scheme. -/
@[stacks 0DTS]
theorem of_locallyQuasiFinite_inertia {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (p : FieldValuedPoint X)
    (h : Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S)
      (forget.{u + 1, u, u, u + 1} X)) :
    IsScheme p :=
  sorry

end IsScheme

end automorphismGroup

end AlgebraicGeometry.AlgebraicStack
