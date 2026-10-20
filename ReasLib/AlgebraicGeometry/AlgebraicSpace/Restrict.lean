module

public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage

/-!
# Restriction of algebraic spaces over a scheme to a base open

An open `V ⊂ Y` of a scheme determines an algebraic space over `Y` together
with the open immersion into `Y`. Restricting a morphism `f : X ⟶ Y` of
algebraic spaces along that immersion recovers
`openInverseImageTo f (ofSchemeOpensι V)`, and modules pull back along
`openInverseImageι f (ofSchemeOpensι V)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The algebraic space over `Y` represented by an open subscheme `V ⊂ Y`. -/
def ofSchemeOpens {Y : Scheme.{u}} (V : Y.Opens) : AlgebraicSpace Y :=
  ofOver (Over.mk V.ι)

/-- `ofSchemeOpens V` is `ofOver` of the open immersion `V.ι`. -/
theorem ofSchemeOpens_eq {Y : Scheme.{u}} (V : Y.Opens) :
    ofSchemeOpens V = ofOver (Over.mk V.ι) :=
  rfl

/-- The open immersion of `ofSchemeOpens V` into `Y`, as a morphism of algebraic
spaces over `Y`. -/
def ofSchemeOpensι {Y : Scheme.{u}} (V : Y.Opens) :
    ofSchemeOpens V ⟶ ofOver (Over.mk (𝟙 Y)) :=
  ofOverHomMk V.ι (Category.comp_id V.ι)

/-- `ofSchemeOpensι V` is `ofOverHomMk` of `V.ι`. -/
theorem ofSchemeOpensι_eq {Y : Scheme.{u}} (V : Y.Opens) :
    ofSchemeOpensι V = ofOverHomMk V.ι (Category.comp_id V.ι) :=
  rfl

/-- The morphism `ofSchemeOpensι V` is an open immersion of algebraic spaces. -/
instance instIsOpenImmersion_ofSchemeOpensι {Y : Scheme.{u}} (V : Y.Opens) :
    IsOpenImmersion (ofSchemeOpensι V) :=
  sorry

/-- The restriction of a morphism of algebraic spaces over a scheme to the
inverse image of a base open. -/
def morphismRestrict {Y : Scheme.{u}} {X : AlgebraicSpace Y}
    (f : X ⟶ ofOver (Over.mk (𝟙 Y))) (V : Y.Opens) :
    openInverseImage f (ofSchemeOpensι V) ⟶ ofSchemeOpens V :=
  openInverseImageTo f (ofSchemeOpensι V)

/-- `morphismRestrict f V` is `openInverseImageTo` along `ofSchemeOpensι V`. -/
theorem morphismRestrict_eq {Y : Scheme.{u}} {X : AlgebraicSpace Y}
    (f : X ⟶ ofOver (Over.mk (𝟙 Y))) (V : Y.Opens) :
    morphismRestrict f V = openInverseImageTo f (ofSchemeOpensι V) :=
  rfl

namespace Modules

/-- The restriction of an `𝒪_X`-module to the inverse image of a base open. -/
def restrictToBasePreimage {Y : Scheme.{u}} {X : AlgebraicSpace Y}
    (f : X ⟶ ofOver (Over.mk (𝟙 Y))) (L : X.Modules) (V : Y.Opens) :
    (openInverseImage f (ofSchemeOpensι V)).Modules :=
  (pullback (openInverseImageι f (ofSchemeOpensι V))).obj L

/-- `restrictToBasePreimage f L V` is module pullback along
`openInverseImageι f (ofSchemeOpensι V)`. -/
theorem restrictToBasePreimage_eq {Y : Scheme.{u}} {X : AlgebraicSpace Y}
    (f : X ⟶ ofOver (Over.mk (𝟙 Y))) (L : X.Modules) (V : Y.Opens) :
    restrictToBasePreimage f L V =
      (pullback (openInverseImageι f (ofSchemeOpensι V))).obj L :=
  rfl

end Modules

end AlgebraicGeometry.AlgebraicSpace
