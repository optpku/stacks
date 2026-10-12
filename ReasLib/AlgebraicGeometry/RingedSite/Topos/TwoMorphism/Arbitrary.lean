/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Hom
import Mathlib.Tactic.CrossRefAttribute

/-!
# `2`-morphisms between arbitrary morphisms of ringed topoi

This is the presentation-independent `2`-cell layer for `RingedSite.ToposHom`.  A `2`-cell is
stored as a natural transformation of direct images.  Its compatibility square is formed in
ring-valued sheaves using the canonical lift of that transformation; compatibility after
forgetting to type-valued sheaves is a derived theorem.  The site-functor specialization remains
in `Topos.TwoMorphism.Basic`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe uX vX uY vY uW vW uZ vZ w

namespace RingedSite.ToposHom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
  [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]

/-- A `2`-morphism between arbitrary morphisms of ringed topoi is a natural transformation
of direct images compatible with the structure-sheaf maps. -/
@[stacks 04IC "arbitrary"]
structure TwoMorphism (f g : ToposHom X Y) where
  /-- The natural transformation between the underlying direct-image functors. -/
  hom : f.toTopos.pushforward ⟶ g.toTopos.pushforward
  /-- Compatibility with the canonical ring-valued direct-image structure maps. -/
  comm :
    f.directStructureMap ≫
        (MorphismOfTopoiIn.ringDirectImageNatTrans hom).app X.structureSheaf =
      g.directStructureMap

/-- After forgetting ring structure, a ringed-topos `2`-morphism commutes with the underlying
direct-image structure maps. -/
theorem TwoMorphism.underlying_comm {f g : ToposHom X Y} (η : TwoMorphism f g) :
    f.underlyingDirectImageMap ≫
        η.hom.app (Hom.underlyingStructureSheaf X) =
      g.underlyingDirectImageMap := sorry

/-- Arbitrary ringed-topos `2`-morphisms are determined by their underlying natural
transformations. -/
@[ext]
theorem TwoMorphism.ext {f g : ToposHom X Y} {η θ : TwoMorphism f g}
    (h : η.hom = θ.hom) : η = θ := sorry

/-- Compatibility of the identity direct-image transformation with the structure map. -/
theorem refl_comm (f : ToposHom X Y) :
    f.directStructureMap ≫
        (MorphismOfTopoiIn.ringDirectImageNatTrans
          (𝟙 f.toTopos.pushforward)).app X.structureSheaf =
      f.directStructureMap := sorry

/-- The identity `2`-morphism of an arbitrary morphism of ringed topoi. -/
def TwoMorphism.refl (f : ToposHom X Y) : TwoMorphism f f where
  hom := 𝟙 f.toTopos.pushforward
  comm := refl_comm f

/-- Compatibility of vertical composition with the structure map. -/
theorem comp_comm {f g h : ToposHom X Y}
    (η : TwoMorphism f g) (θ : TwoMorphism g h) :
    f.directStructureMap ≫
        (MorphismOfTopoiIn.ringDirectImageNatTrans
          (η.hom ≫ θ.hom)).app X.structureSheaf =
      h.directStructureMap := sorry

/-- Vertical composition of arbitrary ringed-topos `2`-morphisms. -/
def TwoMorphism.comp {f g h : ToposHom X Y}
    (η : TwoMorphism f g) (θ : TwoMorphism g h) : TwoMorphism f h where
  hom := η.hom ≫ θ.hom
  comm := comp_comm η θ

section Whiskering

variable {W : RingedSite.{uW, vW, w}} {Z : RingedSite.{uZ, vZ, w}}
variable [W.siteTopology.HasSheafCompose (forget RingCat.{w})]
  [Z.siteTopology.HasSheafCompose (forget RingCat.{w})]

/-- Compatibility of left whiskering with the composite structure map. -/
theorem whiskerLeft_comm (k : ToposHom W X) {f g : ToposHom X Y}
    (η : TwoMorphism f g) :
    (ToposHom.comp k f).directStructureMap ≫
        (MorphismOfTopoiIn.ringDirectImageNatTrans
          (Functor.whiskerLeft k.toTopos.pushforward η.hom)).app W.structureSheaf =
      (ToposHom.comp k g).directStructureMap := sorry

/-- Left whiskering of a ringed-topos `2`-morphism. -/
def TwoMorphism.whiskerLeft (k : ToposHom W X) {f g : ToposHom X Y}
    (η : TwoMorphism f g) :
    TwoMorphism (ToposHom.comp k f) (ToposHom.comp k g) where
  hom := Functor.whiskerLeft k.toTopos.pushforward η.hom
  comm := whiskerLeft_comm k η

/-- Compatibility of right whiskering with the composite structure map. -/
theorem whiskerRight_comm {f g : ToposHom X Y} (η : TwoMorphism f g)
    (h : ToposHom Y Z) :
    (ToposHom.comp f h).directStructureMap ≫
        (MorphismOfTopoiIn.ringDirectImageNatTrans
          (Functor.whiskerRight η.hom h.toTopos.pushforward)).app X.structureSheaf =
      (ToposHom.comp g h).directStructureMap := sorry

/-- Right whiskering of a ringed-topos `2`-morphism. -/
def TwoMorphism.whiskerRight {f g : ToposHom X Y} (η : TwoMorphism f g)
    (h : ToposHom Y Z) :
    TwoMorphism (ToposHom.comp f h) (ToposHom.comp g h) where
  hom := Functor.whiskerRight η.hom h.toTopos.pushforward
  comm := whiskerRight_comm η h

/-- Horizontal composition of ringed-topos `2`-morphisms. -/
def TwoMorphism.hcomp {f g : ToposHom X Y} {h i : ToposHom Y Z}
    (η : TwoMorphism f g) (θ : TwoMorphism h i) :
    TwoMorphism (ToposHom.comp f h) (ToposHom.comp g i) :=
  (η.whiskerRight h).comp (θ.whiskerLeft g)

end Whiskering

/-- An invertible `2`-morphism between arbitrary morphisms of ringed topoi.  Keeping the
natural isomorphism as data makes commutative diagrams reusable without hiding comparison data
behind an existential statement. -/
@[stacks 04IC "invertible"]
structure TwoIso (f g : ToposHom X Y) where
  /-- The natural isomorphism between the underlying direct-image functors. -/
  homIso : f.toTopos.pushforward ≅ g.toTopos.pushforward
  /-- Compatibility with the canonical ring-valued direct-image structure maps. -/
  comm :
    f.directStructureMap ≫
        (MorphismOfTopoiIn.ringDirectImageNatTrans homIso.hom).app X.structureSheaf =
      g.directStructureMap

/-- The identity `2`-isomorphism of a morphism of ringed topoi. -/
def TwoIso.refl (f : ToposHom X Y) : TwoIso f f where
  homIso := Iso.refl _
  comm := refl_comm f

/-- After forgetting ring structure, an invertible ringed-topos `2`-morphism commutes with the
underlying direct-image structure maps. -/
theorem TwoIso.underlying_comm {f g : ToposHom X Y} (e : TwoIso f g) :
    f.underlyingDirectImageMap ≫
        e.homIso.hom.app (Hom.underlyingStructureSheaf X) =
      g.underlyingDirectImageMap := sorry

/-- The forward `2`-morphism underlying an invertible `2`-morphism. -/
def TwoIso.hom {f g : ToposHom X Y} (e : TwoIso f g) : TwoMorphism f g where
  hom := e.homIso.hom
  comm := e.comm

/-- Compatibility of the inverse natural transformation of an invertible `2`-morphism. -/
theorem TwoIso.inv_comm {f g : ToposHom X Y} (e : TwoIso f g) :
    g.directStructureMap ≫
        (MorphismOfTopoiIn.ringDirectImageNatTrans
          e.homIso.inv).app X.structureSheaf =
      f.directStructureMap := sorry

/-- The inverse `2`-morphism underlying an invertible `2`-morphism. -/
def TwoIso.inv {f g : ToposHom X Y} (e : TwoIso f g) : TwoMorphism g f where
  hom := e.homIso.inv
  comm := e.inv_comm

-- The direct-image structure-sheaf map is the ring-valued adjunct of the canonical inverse-image
-- map; only the compatibility fields of the `2`-cell structures carry deferred proof debt.

end RingedSite.ToposHom
