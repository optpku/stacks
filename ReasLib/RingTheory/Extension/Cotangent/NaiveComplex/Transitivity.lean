module

public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Canonical
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.RestrictScalars.Map
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Transitivity for canonical naive cotangent complexes

This leaf specializes target-changing presentation functoriality to the
canonical self-presentations of a tower of commutative rings.  The general
chain-map and parallel-map homotopy mechanisms live in
`Algebra.Extension.NaiveCotangent.RestrictScalars`.
-/

@[expose] public section

open CategoryTheory
open scoped NaiveCotangent

universe u

noncomputable section

namespace Algebra.NaiveCotangent.Transitivity

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

namespace Presentation

/-- The canonical morphism from the self-presentation of `B` over `A` to the
self-presentation of `C` over `B`. -/
@[stacks 07VC "canonical presentation comparison"]
noncomputable def comparison :
    (Generators.self A B).toExtension.Hom (Generators.self B C).toExtension :=
  (Generators.defaultHom
    (Generators.self A B : Generators A B B)
    (Generators.self B C : Generators B C C)).toExtensionHom

/-- The presentation morphism that factors through the coefficient inclusion
`B → B[C]` in the canonical self-presentation of `C` over `B`. -/
@[stacks 07VC "canonical presentation comparison"]
noncomputable def constant :
    (Generators.self A B).toExtension.Hom (Generators.self B C).toExtension :=
  ((Generators.ofComp
      (Generators.self B C : Generators B C C)
      (Generators.self A B : Generators A B B)).comp
    (Generators.toComp
      (Generators.self B C : Generators B C C)
      (Generators.self A B : Generators A B B))).toExtensionHom

end Presentation

/-- The canonical target-changing comparison
`NL{B⁄A} ⟶ NL{C⁄B}↾[B]` for a tower `A → B → C`. -/
@[stacks 07VC "canonical naive cotangent comparison"]
noncomputable def comparison :
    NL{B⁄A} ⟶ NL{C⁄B}↾[B] :=
  Extension.NaiveCotangent.RestrictScalars.map (Presentation.comparison A B C)

/-- The target-changing map induced by the coefficient-only canonical
presentation morphism. -/
@[stacks 07VC "canonical naive cotangent comparison"]
noncomputable def constant :
    NL{B⁄A} ⟶ NL{C⁄B}↾[B] :=
  Extension.NaiveCotangent.RestrictScalars.map (Presentation.constant A B C)

/-- The coefficient-only canonical presentation morphism induces the zero map
of naive cotangent complexes. -/
@[stacks 07VC "canonical naive cotangent comparison"]
theorem constant_eq_zero : constant A B C = 0 := sorry

/-- Remark 10.134.5, tag `07VC`: the canonical comparison
`NL{B⁄A} ⟶ NL{C⁄B}↾[B]` is chain-homotopic to zero.  Its degree-lowering map
is the formal difference between the generator and coefficient presentation
morphisms. -/
@[stacks 07VC "canonical naive cotangent transitivity null-homotopy"]
noncomputable def nullHomotopy : Homotopy (comparison A B C) 0 :=
  (Extension.NaiveCotangent.RestrictScalars.mapHomotopy
    (Presentation.comparison A B C) (Presentation.constant A B C)).trans
    (Homotopy.ofEq (constant_eq_zero A B C))

end Algebra.NaiveCotangent.Transitivity
