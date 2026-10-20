module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Action.Module.Quasicoherent
import StacksCheckRecall

universe u

open AlgebraicGeometry CategoryTheory
open MonoidalCategory AlgebraicSpace.QCoh

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
  (X : GroupAlgebraicSpace.Action G)

/- Definition 78.10.1: The objects of `Equivariant G X` are exactly
`GroupoidAlgebraicSpace.System (GroupoidAlgebraicSpace.ofAction G X)`: pairs
`(F, α)` with `F` a quasi-coherent module on `X.X.left` and a linearization
`α : a^* F ⟶ pr₁^* F`. The cocycle law is the commutative diagram on
`G ×_B G ×_B X` comparing successive pullbacks of `α` along `1_G × a` and
the projection with its pullback along `m × 1_X`. The unit law says that
pullback along `e × 1_X` is the identity on `F`. -/
@[stacks 043T] #check (AlgebraicGeometry.AlgebraicSpace.QCoh.Equivariant G X :
  CategoryTheory.Cat.{u + 1, u + 1})

variable (F : AlgebraicSpace.QCoh X.X.left)
  (α : (AlgebraicSpace.QCoh.pullback (Equivariant.action G X)).obj F ⟶
    (AlgebraicSpace.QCoh.pullback (Equivariant.projection G X)).obj F)
  (D : Equivariant G X)

/- Companion: equivariant quasi-coherent modules are built from a quasi-coherent
module, a linearization, and the cocycle and unit laws. -/
#check (AlgebraicGeometry.AlgebraicSpace.QCoh.Equivariant.of G X F α :
  Equivariant.Cocycle G X F α → Equivariant.Unit G X F α → Equivariant G X)

/- Companion: `obj` and `alpha` recover the underlying module and its
linearization. -/
#check (AlgebraicGeometry.AlgebraicSpace.QCoh.Equivariant.obj :
  Equivariant G X → AlgebraicSpace.QCoh X.X.left)
#check (AlgebraicGeometry.AlgebraicSpace.QCoh.Equivariant.alpha D :
  (AlgebraicSpace.QCoh.pullback (Equivariant.action G X)).obj (Equivariant.obj D) ⟶
    (AlgebraicSpace.QCoh.pullback (Equivariant.projection G X)).obj (Equivariant.obj D))

/- Companion: `spec` packages the cocycle and unit laws. -/
#check (AlgebraicGeometry.AlgebraicSpace.QCoh.Equivariant.spec D :
  Equivariant.Cocycle G X (Equivariant.obj D) (Equivariant.alpha D) ∧
    Equivariant.Unit G X (Equivariant.obj D) (Equivariant.alpha D))

/- Companion: `action` is `a : G ×_B X ⟶ X` and `projection` is
`pr₁ : G ×_B X ⟶ X`. -/
#check (AlgebraicGeometry.AlgebraicSpace.QCoh.Equivariant.action G X :
  (G.X ⊗ X.X).left ⟶ X.X.left)
#check (AlgebraicGeometry.AlgebraicSpace.QCoh.Equivariant.projection G X :
  (G.X ⊗ X.X).left ⟶ X.X.left)

/- Companion: `Cocycle` and `Unit` are the two laws on `(F, α)`. -/
#check (AlgebraicGeometry.AlgebraicSpace.QCoh.Equivariant.Cocycle G X :
  ∀ (F : AlgebraicSpace.QCoh X.X.left),
    ((AlgebraicSpace.QCoh.pullback (Equivariant.action G X)).obj F ⟶
      (AlgebraicSpace.QCoh.pullback (Equivariant.projection G X)).obj F) → Prop)
#check (AlgebraicGeometry.AlgebraicSpace.QCoh.Equivariant.Unit G X :
  ∀ (F : AlgebraicSpace.QCoh X.X.left),
    ((AlgebraicSpace.QCoh.pullback (Equivariant.action G X)).obj F ⟶
      (AlgebraicSpace.QCoh.pullback (Equivariant.projection G X)).obj F) → Prop)
