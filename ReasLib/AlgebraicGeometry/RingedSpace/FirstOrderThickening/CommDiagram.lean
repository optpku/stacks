module

public import Mathlib.CategoryTheory.CommSq
public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening

/-!
# Commutative diagrams of first-order thickenings of ringed spaces

A diagram of ringed spaces whose four horizontal arrows are first-order thickenings, with
commutative back, front, left, and bottom faces. The remaining horizontal morphism
`X'2 ⟶ X'1` is not part of the data.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening

/-- A commutative diagram of morphisms of ringed spaces whose four horizontal arrows are
first-order thickenings. The four complete faces are commutative squares; the morphism
`X'2 ⟶ X'1` is omitted. -/
structure CommDiagram
    {X2 X'2 S2 S'2 X1 X'1 S1 S'1 : RingedSpace.{u}}
    (i2 : X2 ⟶ X'2) (f2 : X2 ⟶ S2) (f'2 : X'2 ⟶ S'2) (t2 : S2 ⟶ S'2)
    (i1 : X1 ⟶ X'1) (f1 : X1 ⟶ S1) (f'1 : X'1 ⟶ S'1) (t1 : S1 ⟶ S'1)
    (g : X2 ⟶ X1) (s : S2 ⟶ S1) (s' : S'2 ⟶ S'1)
    [IsFirstOrderThickening i2] [IsFirstOrderThickening t2]
    [IsFirstOrderThickening i1] [IsFirstOrderThickening t1] : Prop where
  ofCommSqs ::
  /-- The back face on `X2`, `X'2`, `S2`, `S'2`. -/
  back : CommSq i2 f2 f'2 t2
  /-- The front face on `X1`, `X'1`, `S1`, `S'1`. -/
  front : CommSq i1 f1 f'1 t1
  /-- The left face on `X2`, `X1`, `S2`, `S1`. -/
  left : CommSq f2 g s f1
  /-- The bottom face on `S2`, `S'2`, `S1`, `S'1`. -/
  bottom : CommSq t2 s s' t1

namespace CommDiagram

variable {X2 X'2 S2 S'2 X1 X'1 S1 S'1 : RingedSpace.{u}}
variable {i2 : X2 ⟶ X'2} {f2 : X2 ⟶ S2} {f'2 : X'2 ⟶ S'2} {t2 : S2 ⟶ S'2}
variable {i1 : X1 ⟶ X'1} {f1 : X1 ⟶ S1} {f'1 : X'1 ⟶ S'1} {t1 : S1 ⟶ S'1}
variable {g : X2 ⟶ X1} {s : S2 ⟶ S1} {s' : S'2 ⟶ S'1}
variable [IsFirstOrderThickening i2] [IsFirstOrderThickening t2]
variable [IsFirstOrderThickening i1] [IsFirstOrderThickening t1]

/-- Assemble the diagram from the four face equalities. -/
def mk (hback : i2 ≫ f'2 = f2 ≫ t2) (hfront : i1 ≫ f'1 = f1 ≫ t1)
    (hleft : f2 ≫ s = g ≫ f1) (hbottom : t2 ≫ s' = s ≫ t1) :
    CommDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s' :=
  ⟨⟨hback⟩, ⟨hfront⟩, ⟨hleft⟩, ⟨hbottom⟩⟩

/-- The diagram commutes if and only if its four complete faces commute. -/
theorem iff :
    CommDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s' ↔
      CommSq i2 f2 f'2 t2 ∧ CommSq i1 f1 f'1 t1 ∧
        CommSq f2 g s f1 ∧ CommSq t2 s s' t1 := sorry

/-- The morphism of thickenings occupying the back face. -/
def backHom (h : CommDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    of i2 ⟶ of t2 :=
  homMk f2 f'2 h.back.w.symm

/-- The morphism of thickenings occupying the front face. -/
def frontHom (h : CommDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    of i1 ⟶ of t1 :=
  homMk f1 f'1 h.front.w.symm

/-- The morphism of thickenings occupying the base face. -/
def baseHom (h : CommDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') :
    of t2 ⟶ of t1 :=
  homMk s s' h.bottom.w.symm

end CommDiagram

end AlgebraicGeometry.RingedSpace.Thickening
