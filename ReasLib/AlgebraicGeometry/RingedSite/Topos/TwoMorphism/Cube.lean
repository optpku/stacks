module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Square

/-!
# Open cubes of morphisms of ringed topoi

The solid diagram with two commutative squares of ringed topoi, three connecting
morphisms, and invertible `2`-cells on the left and lower faces. The remaining
edge from the upper-right vertex of the back face to the upper-right vertex of
the front face is not part of the data.
-/

@[expose] public section

open CategoryTheory
open RingedSite.ToposHom

noncomputable section

universe uC2 vC2 uC2p vC2p uB2 vB2 uB2p vB2p
  uC1 vC1 uC1p vC1p uB1 vB1 uB1p vB1p w

namespace RingedSite.ToposHom

variable {C2 : RingedSite.{uC2, vC2, w}} {C2' : RingedSite.{uC2p, vC2p, w}}
variable {B2 : RingedSite.{uB2, vB2, w}} {B2' : RingedSite.{uB2p, vB2p, w}}
variable {C1 : RingedSite.{uC1, vC1, w}} {C1' : RingedSite.{uC1p, vC1p, w}}
variable {B1 : RingedSite.{uB1, vB1, w}} {B1' : RingedSite.{uB1p, vB1p, w}}
variable [C2.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [C2'.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [B2.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [B2'.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [C1.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [C1'.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [B1.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [B1'.siteTopology.HasSheafCompose (forget RingCat.{w})]

/-- An open cube of morphisms of ringed topoi consists of two commutative square
faces, three connecting morphisms, and invertible `2`-cells on the left and
lower faces. The remaining edge between the two upper-right vertices is not
part of the data. -/
structure OpenCube (back : CommSquare C2 C2' B2 B2')
    (front : CommSquare C1 C1' B1 B1') where
  /-- The diagonal morphism from the source of the back face to the source of the front face. -/
  g : ToposHom C2 C1
  /-- The connecting morphism between the lower-left vertices of the two faces. -/
  base : ToposHom B2 B1
  /-- The connecting morphism between the lower-right vertices of the two faces. -/
  base' : ToposHom B2' B1'
  /-- The invertible `2`-cell on the left face. -/
  leftCell : TwoIso (ToposHom.comp g front.left) (ToposHom.comp back.left base)
  /-- The invertible `2`-cell on the lower face. -/
  lowerCell : TwoIso (ToposHom.comp back.lower base') (ToposHom.comp base front.lower)

namespace OpenCube

/-- Assemble an open cube from its two commutative faces, connecting morphisms,
and invertible `2`-cells on the left and lower faces. -/
def of (back : CommSquare C2 C2' B2 B2') (front : CommSquare C1 C1' B1 B1')
    (g : ToposHom C2 C1) (base : ToposHom B2 B1) (base' : ToposHom B2' B1')
    (leftCell : TwoIso (ToposHom.comp g front.left) (ToposHom.comp back.left base))
    (lowerCell : TwoIso (ToposHom.comp back.lower base') (ToposHom.comp base front.lower)) :
    OpenCube back front where
  g := g
  base := base
  base' := base'
  leftCell := leftCell
  lowerCell := lowerCell

variable {back : CommSquare C2 C2' B2 B2'} {front : CommSquare C1 C1' B1 B1'}

/-- The commutative square formed by the left edges and the diagonal connecting morphism. -/
def leftSquare (D : OpenCube back front) : CommSquare C2 C1 B2 B1 where
  upper := D.g
  left := back.left
  right := front.left
  lower := D.base
  cell := D.leftCell

/-- The commutative square formed by the lower edges and the two base connecting morphisms. -/
def lowerSquare (D : OpenCube back front) : CommSquare B2 B2' B1 B1' where
  upper := back.lower
  left := D.base
  right := D.base'
  lower := front.lower
  cell := D.lowerCell

/-- The left and lower faces of an open cube recover its connecting morphisms and stored cells. -/
theorem spec (D : OpenCube back front) :
    D.leftSquare.upper = D.g ∧ D.leftSquare.lower = D.base ∧
      D.leftSquare.cell = D.leftCell ∧
      D.lowerSquare.left = D.base ∧ D.lowerSquare.right = D.base' ∧
      D.lowerSquare.cell = D.lowerCell := sorry

end OpenCube

end RingedSite.ToposHom
