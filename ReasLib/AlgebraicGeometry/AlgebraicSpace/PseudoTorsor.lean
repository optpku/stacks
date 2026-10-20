module

public import ReasLib.CategoryTheory.Monoidal.Cartesian.PseudoTorsor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Action

/-!
# Characterizations of pseudo-torsors under group algebraic spaces

An algebraic space with a `G`-action is a pseudo `G`-torsor if and only if, for every
scheme `T` over `B`, the group `G(T)` acts uniquely transitively on `X(T)`. This is the
scheme-points specialization of `Mod.isPseudoTorsor_iff_forall_existsUnique_smul`. A
pseudo `G`-torsor is trivial if and only if `X ⟶ B` is a split epimorphism, equivalently
admits a section.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped ModObj

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace

/-- An algebraic space with `G`-action is a pseudo `G`-torsor if and only if, for every
scheme `T` over `B`, the group `G(T)` acts uniquely transitively on the set `X(T)`. -/
theorem isPseudoTorsor_iff_schemePoints {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (X : Action G) :
    Mod.IsPseudoTorsor X ↔
      ∀ (T : Over S) (t : AlgebraicSpace.ofOver T ⟶ B)
        (x y : Over.mk t ⟶ X.X), ∃! g : Over.mk t ⟶ G.X, g • x = y := sorry

/-- A pseudo `G`-torsor is trivial if and only if its structure morphism is a split
epimorphism. -/
theorem isTrivial_iff_isSplitEpi {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (X : Action G) [Mod.IsPseudoTorsor X] :
    Mod.IsTrivial X ↔ IsSplitEpi X.X.hom := sorry

/-- A pseudo `G`-torsor is trivial if and only if its structure morphism admits a
section. -/
theorem isTrivial_iff_exists_section {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (X : Action G) [Mod.IsPseudoTorsor X] :
    Mod.IsTrivial X ↔ ∃ s : B ⟶ X.X.left, s ≫ X.X.hom = 𝟙 B := sorry

/-- A pseudo `G`-torsor is trivial if and only if there is a morphism over `B` from the
identity object into `X`. -/
theorem isTrivial_iff_nonempty_overHom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (X : Action G) [Mod.IsPseudoTorsor X] :
    Mod.IsTrivial X ↔ Nonempty ((Over.mk (𝟙 B) : Over B) ⟶ X.X) := sorry

end AlgebraicGeometry.GroupAlgebraicSpace
