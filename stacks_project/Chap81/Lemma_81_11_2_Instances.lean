/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
public import stacks_project.Chap81.«81_11_0_1_Glueing»
public import stacks_project.Chap81.Situation_81_10_6_FormalGlueing

/-!
# Conservativity of formal glueing of algebraic spaces

In the formal-glueing situation, the canonical functor
`Over X ⥤ category f i` from 81.11.0.1 reflects isomorphisms.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.FormalGlueing

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FormalGlueing

/-- The canonical functor `Over X ⥤ category f i` reflects isomorphisms. -/
instance functor_reflectsIsomorphisms {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] :
    (functor f i).ReflectsIsomorphisms :=
  sorry

/-- A morphism over `X` is an isomorphism if and only if its image under
the canonical glueing functor is an isomorphism. -/
theorem functor_map_isIso_iff {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] {X₁ X₂ : Over X} (φ : X₁ ⟶ X₂) :
    IsIso ((functor f i).map φ) ↔ IsIso φ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FormalGlueing
