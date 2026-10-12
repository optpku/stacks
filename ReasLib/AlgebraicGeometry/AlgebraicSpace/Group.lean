/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CartesianMonoidal

/-! Internal group objects in slices of algebraic spaces. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry

/-- A group algebraic space over `B` is an internal group object in `Over B`. -/
abbrev GroupAlgebraicSpace {S : Scheme.{u}} (B : AlgebraicSpace S) : Type (u + 1) :=
  Grp (Over B)

namespace GroupAlgebraicSpace

/-- Scheme-valued points of an internal group object form a group. -/
instance schemePoints_group {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (T : Over S) (t : AlgebraicSpace.ofOver T ⟶ B) :
    Group (Over.mk t ⟶ G.X) :=
  Hom.group

/-- An underlying morphism is induced by a morphism of internal monoid objects exactly when it
is the underlying morphism of a group-object morphism. -/
theorem hom_iff_isMonHom {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G G' : GroupAlgebraicSpace B} (ψ : G.X ⟶ G'.X) :
    (∃ φ : G ⟶ G', φ.hom.hom = ψ) ↔ IsMonHom ψ := sorry

/-- An underlying morphism preserves multiplication exactly when it induces homomorphisms on all
scheme-valued points. -/
theorem hom_iff_schemePoints {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G G' : GroupAlgebraicSpace B} (ψ : G.X ⟶ G'.X) :
    IsMonHom ψ ↔
      ∀ (T : Over S) (t : AlgebraicSpace.ofOver T ⟶ B),
        ∀ a b : Over.mk t ⟶ G.X, (a ≫ ψ) * (b ≫ ψ) = (a * b) ≫ ψ := sorry

end GroupAlgebraicSpace

end AlgebraicGeometry
