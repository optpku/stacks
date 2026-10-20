module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Group

/-!
# Actions of group algebraic spaces

An action of a group algebraic space `G` over an algebraic space `B` is a module
object for `G.X` in the cartesian monoidal slice `Over B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace

/-- The category of actions of a group algebraic space over `B`, with `G`-equivariant
morphisms. -/
abbrev Action {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B) :=
  Mod (Over B) G.X

namespace Action

/-- The bundled `G`-action associated to a module object structure on an algebraic
space over `B`. -/
def of {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    (X : Over B) [ModObj G.X X] : Action G where
  X := X

/-- The underlying algebraic space over `B` of `Action.of G X` is `X`. -/
theorem of_X {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    (X : Over B) [ModObj G.X X] : (of G X).X = X := sorry

/-- A morphism of underlying algebraic spaces over `B` is a morphism of `G`-actions
if and only if it is a morphism of module objects. -/
theorem hom_iff_isModHom {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupAlgebraicSpace B} {X Y : Action G} (ψ : X.X ⟶ Y.X) :
    (∃ φ : X ⟶ Y, φ.hom = ψ) ↔ IsModHom G.X ψ := sorry

/-- A morphism of underlying algebraic spaces over `B` is `G`-equivariant if and only
if it induces a map of `G(T)`-sets on scheme-valued points. -/
theorem hom_iff_schemePoints {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupAlgebraicSpace B} {X Y : Action G} (ψ : X.X ⟶ Y.X) :
    IsModHom G.X ψ ↔
      ∀ (T : Over S) (t : AlgebraicSpace.ofOver T ⟶ B),
        ∀ (g : Over.mk t ⟶ G.X) (x : Over.mk t ⟶ X.X),
          (g • x) ≫ ψ = g • (x ≫ ψ) := sorry

end Action

end AlgebraicGeometry.GroupAlgebraicSpace
