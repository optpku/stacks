module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Square

/-!
# Open cubes of morphisms of ringed topoi

The solid diagram with two commutative squares of ringed topoi, three connecting
morphisms, and invertible `2`-cells on the left and lower faces. The remaining
edge from `(Sh(C'2), O'2)` to `(Sh(C'1), O'1)` is not part of the data.
-/

@[expose] public section

open CategoryTheory
open RingedSite.ToposHom

noncomputable section

universe u v w

namespace RingedSite.ToposHom

variable {C2 C2' B2 B2' : RingedSite.{u, v, w}}
variable {C1 C1' B1 B1' : RingedSite.{u, v, w}}
variable [C2.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [C2'.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [B2.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [B2'.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [C1.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [C1'.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [B1.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [B1'.siteTopology.HasSheafCompose (forget RingCat.{w})]

/-- An open cube of morphisms of ringed topoi: back and front commutative
squares, connecting morphisms `g`, `base`, and `base'`, and invertible `2`-cells
on the left and lower faces. The remaining edge `(Sh(C'2), O'2) ⟶ (Sh(C'1), O'1)`
is not part of the data. -/
structure OpenCube (back : CommSquare C2 C2' B2 B2')
    (front : CommSquare C1 C1' B1 B1') where
  /-- The named diagonal morphism `g : (Sh(C2), O2) ⟶ (Sh(C1), O1)`. -/
  g : ToposHom C2 C1
  /-- The unlabeled base morphism `(Sh(B2), O_{B2}) ⟶ (Sh(B1), O_{B1})`. -/
  base : ToposHom B2 B1
  /-- The unlabeled primed base morphism `(Sh(B'2), O_{B'2}) ⟶ (Sh(B'1), O_{B'1})`. -/
  base' : ToposHom B2' B1'
  /-- The invertible `2`-cell on the left face, from `comp g front.left` to
  `comp back.left base`. -/
  leftCell : TwoIso (ToposHom.comp g front.left) (ToposHom.comp back.left base)
  /-- The invertible `2`-cell on the lower face, from `comp back.lower base'` to
  `comp base front.lower`. -/
  lowerCell :
    TwoIso (ToposHom.comp back.lower base') (ToposHom.comp base front.lower)

namespace OpenCube

/-- Assemble an open cube from its back and front faces, connecting morphisms,
and face `2`-isomorphisms. -/
def of (back : CommSquare C2 C2' B2 B2') (front : CommSquare C1 C1' B1 B1')
    (g : ToposHom C2 C1) (base : ToposHom B2 B1) (base' : ToposHom B2' B1')
    (leftCell : TwoIso (ToposHom.comp g front.left) (ToposHom.comp back.left base))
    (lowerCell :
      TwoIso (ToposHom.comp back.lower base') (ToposHom.comp base front.lower)) :
    OpenCube back front where
  g := g
  base := base
  base' := base'
  leftCell := leftCell
  lowerCell := lowerCell

variable {back : CommSquare C2 C2' B2 B2'} {front : CommSquare C1 C1' B1 B1'}

/-- The left face on `(Sh(C2), O2)`, `(Sh(C1), O1)`, `(Sh(B2), O_{B2})`,
`(Sh(B1), O_{B1})`. -/
def leftSquare (D : OpenCube back front) : CommSquare C2 C1 B2 B1 where
  upper := D.g
  left := back.left
  right := front.left
  lower := D.base
  cell := D.leftCell

/-- The lower face on `(Sh(B2), O_{B2})`, `(Sh(B'2), O_{B'2})`, `(Sh(B1), O_{B1})`,
`(Sh(B'1), O_{B'1})`. -/
def lowerSquare (D : OpenCube back front) : CommSquare B2 B2' B1 B1' where
  upper := back.lower
  left := D.base
  right := D.base'
  lower := front.lower
  cell := D.lowerCell

/-- The connecting morphisms of an open cube occupy the left and lower faces,
with the stored `2`-isomorphisms as those face cells. -/
theorem spec (D : OpenCube back front) :
    D.leftSquare.upper = D.g ∧ D.leftSquare.lower = D.base ∧
      D.leftSquare.cell = D.leftCell ∧
      D.lowerSquare.left = D.base ∧ D.lowerSquare.right = D.base' ∧
      D.lowerSquare.cell = D.lowerCell := sorry

/-- The source-named upper edge `i2` of the back face. -/
abbrev i2 : ToposHom C2 C2' := back.upper

/-- The source-named upper edge `i1` of the front face. -/
abbrev i1 : ToposHom C1 C1' := front.upper

/-- The source-named lower edge `t2` of the back face. -/
abbrev t2 : ToposHom B2 B2' := back.lower

/-- The source-named lower edge `t1` of the front face. -/
abbrev t1 : ToposHom B1 B1' := front.lower

/-- The source-named left edge `f2` of the back face. -/
abbrev f2 : ToposHom C2 B2 := back.left

/-- The source-named left edge `f1` of the front face. -/
abbrev f1 : ToposHom C1 B1 := front.left

/-- The source-named right edge `f'2` of the back face. -/
abbrev f2' : ToposHom C2' B2' := back.right

/-- The source-named right edge `f'1` of the front face. -/
abbrev f1' : ToposHom C1' B1' := front.right

end OpenCube

end RingedSite.ToposHom
