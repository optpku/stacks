module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.RelativeIsom.Action
public import ReasLib.AlgebraicGeometry.AlgebraicStack.RelativeIsom.Comparison
import StacksCheckRecall

/-!
# Lemma 101.5.4

For a morphism of algebraic stacks and morphisms from an algebraic space, the
relative automorphism sheaf is a group algebraic space, it sits in a left-exact
sequence of groups, relative isomorphisms arise by cartesian pullback along a
2-morphism, and that relative isomorphism space is a pseudo-torsor for the
relative automorphism sheaf.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Bicategory
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.RelativeIsom

/- Lemma 101.5.4 (1): relative automorphisms form a group algebraic space over Z. -/
@[stacks 0CPK] #check
  (AlgebraicGeometry.AlgebraicStack.RelativeIsom.instGrpObj_asHomotopy :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
      {Z : AlgebraicSpace S} (x2 : Z.toGroupoids ⟶ X),
      GrpObj (asHomotopy f x2))

/- Lemma 101.5.4 (2): relative automorphisms are the kernel of the canonical map
from absolute automorphisms to automorphisms of their image. -/
@[stacks 0CPK] #check
  (AlgebraicGeometry.AlgebraicStack.RelativeIsom.isomExactSequence :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
      {Z : AlgebraicSpace S} (x2 : Z.toGroupoids ⟶ X)
      {G : Bicategory.HomotopyCategory (SpacesOver Z.toGroupoids)}
      (φ : G ⟶ asHomotopy (baseProjection.{u + 1, u, u + 1} X) x2),
      (∃! ψ : G ⟶ asHomotopy f x2, ψ ≫ kernelι f x2 = φ) ↔
        φ ≫ toTarget f x2 = φ ≫ constOne f x2)

/- Lemma 101.5.4 (3): the relative Isom space is the cartesian fibre of the
map between same-base Isom spaces above the section defined by α. -/
@[stacks 0CPK] #check
  (AlgebraicGeometry.AlgebraicStack.RelativeIsom.comparisonCone_isBilimit :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
      {Z : AlgebraicSpace S} {x1 x2 : Z.toGroupoids ⟶ X}
      (α : x1 ≫ f ≅ x2 ≫ f), (comparisonCone f α).IsBilimit)

/- Lemma 101.5.4 (4): relative isomorphisms with prescribed image form a
pseudo-torsor under relative automorphisms of the second morphism. -/
@[stacks 0CPK] #check
  (AlgebraicGeometry.AlgebraicStack.RelativeIsom.instIsPseudoTorsor_action :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
      {Z : AlgebraicSpace S} {x1 x2 : Z.toGroupoids ⟶ X}
      (α : x1 ≫ f ≅ x2 ≫ f), Mod.IsPseudoTorsor (action f α))

end AlgebraicGeometry.AlgebraicStack.RelativeIsom
