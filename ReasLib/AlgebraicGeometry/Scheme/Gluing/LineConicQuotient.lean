/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.LineConic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.GenericPoints
public import ReasLib.AlgebraicGeometry.Scheme.OverField

/-!
# Identification quotients of a line and a conic in projective 3-space

A scheme identifying a line in `ℙ³_k` with a disjoint isomorphic conic is specified by
a proper birational morphism and its behavior on the curves and their complement.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProjectiveSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- A morphism `π : ℙ³_k ⟶ X` exhibits `X` as an identification of a line with a conic along
`φ` when it is a surjective proper birational morphism over `k` which is an isomorphism off the
two curves and identifies them via `φ`. -/
structure IsLineConicQuotient {k : Type u} [Field k] {L C : Scheme.{u}}
    (iL : L ⟶ scheme k 3) (iC : C ⟶ scheme k 3) (φ : L ⟶ C)
    (X : SchemeOverField k) (π : scheme k 3 ⟶ X.left) (U : X.left.Opens) : Prop where
  /-- `π` is a morphism of schemes over `Spec k`. -/
  over_base : π ≫ X.hom = toSpec k 3
  /-- `π` is surjective. -/
  surjective : Surjective π
  /-- `π` is proper. -/
  isProper : IsProper π
  /-- `π` is birational. -/
  isBirational : IsBirational π
  /-- `π` restricts to an isomorphism over `U`. -/
  isoOnOpen : IsIso (π ∣_ U)
  /-- The preimage of `U` is the complement of the line and the conic. -/
  preimage_eq : (π ⁻¹ᵁ U : Set (scheme k 3)) = (Set.range iL ∪ Set.range iC)ᶜ
  /-- `π` identifies the line with the conic along `φ`. -/
  glue : iL ≫ π = φ ≫ iC ≫ π

/-- The seven comparison properties define a line-conic identification quotient. -/
def IsLineConicQuotient.of {k : Type u} [Field k] {L C : Scheme.{u}}
    (iL : L ⟶ scheme k 3) (iC : C ⟶ scheme k 3) (φ : L ⟶ C)
    (X : SchemeOverField k) (π : scheme k 3 ⟶ X.left) (U : X.left.Opens)
    (over_base : π ≫ X.hom = toSpec k 3) (surjective : Surjective π)
    (isProper : IsProper π) (isBirational : IsBirational π)
    (isoOnOpen : IsIso (π ∣_ U))
    (preimage_eq : (π ⁻¹ᵁ U : Set (scheme k 3)) = (Set.range iL ∪ Set.range iC)ᶜ)
    (glue : iL ≫ π = φ ≫ iC ≫ π) :
    IsLineConicQuotient iL iC φ X π U where
  over_base := over_base
  surjective := surjective
  isProper := isProper
  isBirational := isBirational
  isoOnOpen := isoOnOpen
  preimage_eq := preimage_eq
  glue := glue

/-- The identification-quotient specification is equivalent to the seven comparison axioms. -/
theorem isLineConicQuotient_iff {k : Type u} [Field k] {L C : Scheme.{u}}
    (iL : L ⟶ scheme k 3) (iC : C ⟶ scheme k 3) (φ : L ⟶ C)
    (X : SchemeOverField k) (π : scheme k 3 ⟶ X.left) (U : X.left.Opens) :
    IsLineConicQuotient iL iC φ X π U ↔
      π ≫ X.hom = toSpec k 3 ∧ Surjective π ∧ IsProper π ∧ IsBirational π ∧
        IsIso (π ∣_ U) ∧
          (π ⁻¹ᵁ U : Set (scheme k 3)) = (Set.range iL ∪ Set.range iC)ᶜ ∧
            iL ≫ π = φ ≫ iC ≫ π := sorry

end AlgebraicGeometry
