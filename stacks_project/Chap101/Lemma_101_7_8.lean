module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.QuasiCompact.Permanence
public import ReasLib.AlgebraicGeometry.AlgebraicStack.QuasiSeparated.Permanence
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open Bicategory
open scoped Bicategory

universe u

/- Lemma 101.7.8 (1): if `X` is quasi-compact and `Y` is quasi-separated, then `f`
is quasi-compact. -/
@[stacks 075S] #check
  (AlgebraicGeometry.AlgebraicStack.QuasiCompact.of_isQuasiCompact :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
      [IsQuasiCompact X] [IsQuasiSeparated Y],
      QuasiCompact f)

/- Lemma 101.7.8 (2): if `X` is quasi-compact and quasi-separated and `Y` is
quasi-separated, then `f` is quasi-compact and quasi-separated. -/
@[stacks 075S] #check
  (AlgebraicGeometry.AlgebraicStack.QuasiCompact.of_isQuasiCompact :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
      [IsQuasiCompact X] [IsQuasiSeparated Y],
      QuasiCompact f)

@[stacks 075S] #check
  (AlgebraicGeometry.AlgebraicStack.QuasiSeparated.of_isQuasiSeparated :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
      [IsQuasiSeparated X] [IsQuasiSeparated Y],
      QuasiSeparated f)

/- Lemma 101.7.8 (3): a 2-fibre product of quasi-compact and quasi-separated
algebraic stacks is quasi-compact and quasi-separated. -/
@[stacks 075S] #check
  (AlgebraicGeometry.AlgebraicStack.IsQuasiCompact.of_isBilimit :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
      {f : X ⟶ Y} {g : Z ⟶ Y}
      [IsQuasiCompact X] [IsQuasiSeparated Y] [IsQuasiCompact Z]
      (c : PseudoPullbackCone f g) [AlgebraicStack c.pt],
      c.IsBilimit → IsQuasiCompact c.pt)

@[stacks 075S] #check
  (AlgebraicGeometry.AlgebraicStack.IsQuasiSeparated.of_isBilimit :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
      {f : X ⟶ Y} {g : Z ⟶ Y}
      [IsQuasiSeparated X] [IsQuasiSeparated Y] [IsQuasiSeparated Z]
      (c : PseudoPullbackCone f g) [AlgebraicStack c.pt],
      c.IsBilimit → IsQuasiSeparated c.pt)

@[stacks 075S] #check
  (AlgebraicGeometry.AlgebraicStack.IsQuasiCompact.instTwoFibreProduct :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
      (f : X ⟶ Y) (g : Z ⟶ Y)
      [IsQuasiCompact X] [IsQuasiSeparated Y] [IsQuasiCompact Z]
      [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)],
      IsQuasiCompact (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g))

@[stacks 075S] #check
  (AlgebraicGeometry.AlgebraicStack.IsQuasiSeparated.instTwoFibreProduct :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
      (f : X ⟶ Y) (g : Z ⟶ Y)
      [IsQuasiSeparated X] [IsQuasiSeparated Y] [IsQuasiSeparated Z]
      [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)],
      IsQuasiSeparated (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g))
