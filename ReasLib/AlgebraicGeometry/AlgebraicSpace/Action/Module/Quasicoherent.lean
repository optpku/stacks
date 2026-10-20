module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Action
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quasicoherent

/-!
# Equivariant quasi-coherent sheaves on algebraic spaces

A quasi-coherent `G`-equivariant sheaf on an algebraic space with `G`-action is a
quasi-coherent module on the associated action groupoid.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QCoh.Equivariant

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- The action map `G ×_B X ⟶ X` of a bundled action of a group algebraic space. -/
abbrev action (G : GroupAlgebraicSpace B) (X : GroupAlgebraicSpace.Action G) :
    (G.X ⊗ X.X).left ⟶ X.X.left :=
  (GroupoidAlgebraicSpace.ofAction G X).t.left

/-- The projection `G ×_B X ⟶ X` from the product carrying an action. -/
abbrev projection (G : GroupAlgebraicSpace B) (X : GroupAlgebraicSpace.Action G) :
    (G.X ⊗ X.X).left ⟶ X.X.left :=
  (GroupoidAlgebraicSpace.ofAction G X).s.left

/-- The cocycle condition for a `G`-linearization, viewed through the action groupoid. -/
abbrev Cocycle (G : GroupAlgebraicSpace B) (X : GroupAlgebraicSpace.Action G)
    (F : AlgebraicSpace.QCoh X.X.left)
    (alpha : (AlgebraicSpace.QCoh.pullback (action G X)).obj F ⟶
      (AlgebraicSpace.QCoh.pullback (projection G X)).obj F) : Prop :=
  GroupoidAlgebraicSpace.Cocycle (GroupoidAlgebraicSpace.ofAction G X) F alpha

/-- The unit condition for a `G`-linearization, viewed through the action groupoid. -/
abbrev Unit (G : GroupAlgebraicSpace B) (X : GroupAlgebraicSpace.Action G)
    (F : AlgebraicSpace.QCoh X.X.left)
    (alpha : (AlgebraicSpace.QCoh.pullback (action G X)).obj F ⟶
      (AlgebraicSpace.QCoh.pullback (projection G X)).obj F) : Prop :=
  GroupoidAlgebraicSpace.Unit (GroupoidAlgebraicSpace.ofAction G X) F alpha

end AlgebraicGeometry.AlgebraicSpace.QCoh.Equivariant

namespace AlgebraicGeometry.AlgebraicSpace.QCoh

/-- The category of quasi-coherent `G`-equivariant sheaves on an algebraic space with
`G`-action, realized as quasi-coherent modules on the associated action groupoid. -/
abbrev Equivariant {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    (X : GroupAlgebraicSpace.Action G) : Cat :=
  GroupoidAlgebraicSpace.QCoh (GroupoidAlgebraicSpace.ofAction G X)

namespace Equivariant

/-- Construct a `G`-equivariant quasi-coherent sheaf from explicit linearization data. -/
abbrev of {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    (X : GroupAlgebraicSpace.Action G) (F : AlgebraicSpace.QCoh X.X.left)
    (alpha : (AlgebraicSpace.QCoh.pullback (action G X)).obj F ⟶
      (AlgebraicSpace.QCoh.pullback (projection G X)).obj F)
    (cocycle : Cocycle G X F alpha) (unit : Unit G X F alpha) : Equivariant G X :=
  GroupoidAlgebraicSpace.QCoh.of F alpha cocycle unit

/-- The underlying quasi-coherent module of an equivariant object. -/
abbrev obj {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupAlgebraicSpace B}
    {X : GroupAlgebraicSpace.Action G} (D : Equivariant G X) :
    AlgebraicSpace.QCoh X.X.left :=
  GroupoidAlgebraicSpace.QCoh.obj D

/-- The linearization of an equivariant object. -/
abbrev alpha {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupAlgebraicSpace B}
    {X : GroupAlgebraicSpace.Action G} (D : Equivariant G X) :
    (AlgebraicSpace.QCoh.pullback (action G X)).obj (obj D) ⟶
      (AlgebraicSpace.QCoh.pullback (projection G X)).obj (obj D) :=
  GroupoidAlgebraicSpace.QCoh.action D

/-- The underlying quasi-coherent-module map of an equivariant morphism. -/
abbrev hom {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupAlgebraicSpace B}
    {X : GroupAlgebraicSpace.Action G} {A B : Equivariant G X} (f : A ⟶ B) :
    obj A ⟶ obj B :=
  GroupoidAlgebraicSpace.QCoh.hom f

/-- An equivariant sheaf satisfies its cocycle and unit laws. -/
theorem spec {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupAlgebraicSpace B}
    {X : GroupAlgebraicSpace.Action G} (D : Equivariant G X) :
    Cocycle G X (obj D) (alpha D) ∧ Unit G X (obj D) (alpha D) :=
  sorry

/-- Equivariant quasi-coherent sheaves identify with quasi-coherent modules on the action
groupoid by the identity on their underlying modules, linearizations, and morphisms. -/
def equivalenceActionGroupoid {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (X : GroupAlgebraicSpace.Action G) :
    Equivariant G X ≌ GroupoidAlgebraicSpace.QCoh (GroupoidAlgebraicSpace.ofAction G X) :=
  CategoryTheory.Equivalence.refl

end Equivariant

end AlgebraicGeometry.AlgebraicSpace.QCoh
