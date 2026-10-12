/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.GenericPoints
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.OpenSubschemes
public import ReasLib.AlgebraicGeometry.Scheme.OverField.FunctionField

/-!
# Birational varieties over a field

This file relates birationality of varieties over a field to their function
fields, open subschemes, and birational morphisms from open subschemes.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- An open subscheme of `X` admits a birational morphism to `Y` over the base field. -/
def HasBirationalOpenTo (X Y : SchemeOverField k) : Prop :=
  ∃ U : X.left.Opens,
    ∃ f : Over.mk (U.ι ≫ X.hom) ⟶ Y, IsBirational f.left

/-- Two varieties over a field are birational exactly when their function fields are isomorphic
as algebras over that field. -/
theorem birationalOver_iff_functionFieldIso
    (X Y : SchemeOverField k) [Variety X] [Variety Y] :
    Scheme.BirationalOver X.hom Y.hom ↔
      Nonempty (functionFieldCommAlg X ≅ functionFieldCommAlg Y) := sorry

/-- Two varieties over a field are birational exactly when an open subscheme of the first admits
a birational morphism to the second over the field. -/
theorem birationalOver_iff_hasBirationalOpenTo
    (X Y : SchemeOverField k) [Variety X] [Variety Y] :
    Scheme.BirationalOver X.hom Y.hom ↔ HasBirationalOpenTo X Y := sorry

/-- For varieties over a field, birationality, isomorphism of function fields, isomorphic
nonempty open subschemes, and a birational morphism from an open subscheme are equivalent. -/
@[stacks 0BXP]
theorem birational_tfae
    (X Y : SchemeOverField k) [Variety X] [Variety Y] :
    List.TFAE
      [ Scheme.BirationalOver X.hom Y.hom
      , Nonempty (functionFieldCommAlg X ≅ functionFieldCommAlg Y)
      , HasIsomorphicNonemptyOpenSubschemesOver (Spec (CommRingCat.of k)) X.left Y.left
      , HasBirationalOpenTo X Y
      ] := sorry

end AlgebraicGeometry.SchemeOverField
