module

import stacks_project.Chap59.Lemma_59_98_1
import ReasLib.AlgebraicGeometry.Scheme.Gluing.Basis.StandardOpen

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open CategoryTheory.GrothendieckTopology.Derived
open CategoryTheory.GrothendieckTopology.Derived.Sections.MayerVietoris
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

#check Scheme.affineBasicOpen
#check Scheme.affineBasicOpen_le
#check Scheme.basicOpen_mul
#check ObjectProperty.homMk
#check CategoryTheory.homOfLE
#check AlgebraicGeometry.Scheme.AffineBasis.emptyObj
#check AlgebraicGeometry.Scheme.AffineBasis.obj
#check siteAbelianSectionsDerived
#check Absolute.rightDerived

example {X : Scheme.{u}} (U : X.affineOpens) : X.smallAffineZariskiSite :=
  { obj := (U : X.Opens), property := U.2 }

example {X : Scheme.{u}} (U : X.affineOpens) : BasisOpen X.affineOpens :=
  AlgebraicGeometry.Scheme.AffineBasis.obj U

example {X : Scheme.{u}} : X.smallAffineZariskiSite :=
  AlgebraicGeometry.Scheme.AffineBasis.emptyObj X

example {X : Scheme.{u}} (U : X.affineOpens) (f g : Γ(X, U)) :
    X.affineBasicOpen (f * g) ≤ X.affineBasicOpen f := by
  exact (Scheme.basicOpen_mul X f g).trans_le inf_le_left

def fooLeft {X : Scheme.{u}} (U : X.affineOpens) (f g : Γ(X, U)) :
    (X.affineBasicOpen (f * g) : X.Opens) ≤ (X.affineBasicOpen f : X.Opens) :=
  (Scheme.basicOpen_mul X f g).trans_le inf_le_left

def fooRight {X : Scheme.{u}} (U : X.affineOpens) (f g : Γ(X, U)) :
    (X.affineBasicOpen (f * g) : X.Opens) ≤ (X.affineBasicOpen g : X.Opens) :=
  (Scheme.basicOpen_mul X f g).trans_le inf_le_right

def fooToY {X : Scheme.{u}} (U : X.affineOpens) (f g : Γ(X, U)) :
    ({ obj := (X.affineBasicOpen (f * g) : X.Opens), property := (X.affineBasicOpen (f * g)).2 } :
      X.smallAffineZariskiSite) ⟶
      { obj := (X.affineBasicOpen f : X.Opens), property := (X.affineBasicOpen f).2 } :=
  ObjectProperty.homMk (homOfLE ((Scheme.basicOpen_mul X f g).trans_le inf_le_left))

lemma fooComm3 {X : Scheme.{u}} (U : X.affineOpens) (f g : Γ(X, U)) :
    (ObjectProperty.homMk
      (homOfLE ((Scheme.basicOpen_mul X f g).trans_le inf_le_left)) :
      ({ obj := (X.affineBasicOpen (f * g) : X.Opens), property := (X.affineBasicOpen (f * g)).2 } :
        X.smallAffineZariskiSite) ⟶
        { obj := (X.affineBasicOpen f : X.Opens), property := (X.affineBasicOpen f).2 }) ≫
      (ObjectProperty.homMk (homOfLE (Scheme.affineBasicOpen_le X f)) :
        ({ obj := (X.affineBasicOpen f : X.Opens), property := (X.affineBasicOpen f).2 } :
          X.smallAffineZariskiSite) ⟶
          { obj := (U : X.Opens), property := U.2 }) =
    (ObjectProperty.homMk
      (homOfLE ((Scheme.basicOpen_mul X f g).trans_le inf_le_right)) :
      ({ obj := (X.affineBasicOpen (f * g) : X.Opens), property := (X.affineBasicOpen (f * g)).2 } :
        X.smallAffineZariskiSite) ⟶
        { obj := (X.affineBasicOpen g : X.Opens), property := (X.affineBasicOpen g).2 }) ≫
      (ObjectProperty.homMk (homOfLE (Scheme.affineBasicOpen_le X g)) :
        ({ obj := (X.affineBasicOpen g : X.Opens), property := (X.affineBasicOpen g).2 } :
          X.smallAffineZariskiSite) ⟶
          { obj := (U : X.Opens), property := U.2 }) := sorry

def fooInY {X : Scheme.{u}} (U : X.affineOpens) (f : Γ(X, U)) :
    ({ obj := (X.affineBasicOpen f : X.Opens), property := (X.affineBasicOpen f).2 } :
      X.smallAffineZariskiSite) ⟶
      { obj := (U : X.Opens), property := U.2 } :=
  ObjectProperty.homMk (homOfLE (Scheme.affineBasicOpen_le X f))

lemma fooComm2 {X : Scheme.{u}} (U : X.affineOpens) (f g : Γ(X, U)) :
    fooToY U f g ≫ fooInY U f =
      (ObjectProperty.homMk (homOfLE ((Scheme.basicOpen_mul X f g).trans_le inf_le_right)) :
        ({ obj := (X.affineBasicOpen (f * g) : X.Opens), property := (X.affineBasicOpen (f * g)).2 } :
          X.smallAffineZariskiSite) ⟶
          { obj := (X.affineBasicOpen g : X.Opens), property := (X.affineBasicOpen g).2 }) ≫
        (ObjectProperty.homMk (homOfLE (Scheme.affineBasicOpen_le X g)) :
          ({ obj := (X.affineBasicOpen g : X.Opens), property := (X.affineBasicOpen g).2 } :
            X.smallAffineZariskiSite) ⟶
            { obj := (U : X.Opens), property := U.2 }) := sorry

def fooSquare {X : Scheme.{u}} (U : X.affineOpens) (f g : Γ(X, U))
    (hU : (U : X.Opens) = X.basicOpen f ⊔ X.basicOpen g) :
    Square X.smallAffineZariskiSite where
  E := { obj := (X.affineBasicOpen (f * g) : X.Opens), property := (X.affineBasicOpen (f * g)).2 }
  Y := { obj := (X.affineBasicOpen f : X.Opens), property := (X.affineBasicOpen f).2 }
  Z := { obj := (X.affineBasicOpen g : X.Opens), property := (X.affineBasicOpen g).2 }
  X := { obj := (U : X.Opens), property := U.2 }
  toY := ObjectProperty.homMk (homOfLE (fooLeft U f g))
  toZ := ObjectProperty.homMk (homOfLE (fooRight U f g))
  inY := ObjectProperty.homMk (homOfLE (Scheme.affineBasicOpen_le X f))
  inZ := ObjectProperty.homMk (homOfLE (Scheme.affineBasicOpen_le X g))
  comm := fooComm2 U f g

def fooSquare2 {X : Scheme.{u}} (U : X.affineOpens) (f g : Γ(X, U))
    (hU : (U : X.Opens) = X.basicOpen f ⊔ X.basicOpen g) :
    Square X.smallAffineZariskiSite where
  E := AlgebraicGeometry.Scheme.AffineBasis.obj (X.affineBasicOpen (f * g))
  Y := AlgebraicGeometry.Scheme.AffineBasis.obj (X.affineBasicOpen f)
  Z := AlgebraicGeometry.Scheme.AffineBasis.obj (X.affineBasicOpen g)
  X := AlgebraicGeometry.Scheme.AffineBasis.obj U
  toY := ObjectProperty.homMk
    (homOfLE ((Scheme.basicOpen_mul X f g).trans_le inf_le_left))
  toZ := ObjectProperty.homMk
    (homOfLE ((Scheme.basicOpen_mul X f g).trans_le inf_le_right))
  inY := ObjectProperty.homMk (homOfLE (Scheme.affineBasicOpen_le X f))
  inZ := ObjectProperty.homMk (homOfLE (Scheme.affineBasicOpen_le X g))
  comm := Subsingleton.elim _ _

example {X : Scheme.{u}}
    [HasWeakSheafify (⊥ : GrothendieckTopology X.smallAffineZariskiSite)
      AddCommGrpCat.{u}]
    [HasSheafify (⊥ : GrothendieckTopology X.smallAffineZariskiSite)
      AddCommGrpCat.{u}]
    [HasSheafify X.smallAffineZariskiTopology AddCommGrpCat.{u}]
    [IsGrothendieckAbelian
      (SiteAbelianSheafCat (⊥ : GrothendieckTopology X.smallAffineZariskiSite))]
    [Functor.HasRightDerivedFunctor
      (Functor.Homotopy.toDerived
        (Absolute.pushforward
          (bot_le : (⊥ : GrothendieckTopology X.smallAffineZariskiSite) ≤
            X.smallAffineZariskiTopology)))
      (Absolute.qis X.smallAffineZariskiTopology)]
    (K : DerivedCategory.Plus
      (SiteAbelianSheafCat (⊥ : GrothendieckTopology X.smallAffineZariskiSite))) :
    Functor.essImage
        (Absolute.rightDerived
          (bot_le : (⊥ : GrothendieckTopology X.smallAffineZariskiSite) ≤
            X.smallAffineZariskiTopology))
        (DerivedCategory.Plus.ι.obj K) ↔
      IsZero
          ((siteAbelianSectionsDerived
              (⊥ : GrothendieckTopology X.smallAffineZariskiSite)
              (AlgebraicGeometry.Scheme.AffineBasis.emptyObj X)).obj
            (DerivedCategory.Plus.ι.obj K)) ∧
        ∀ (U : X.affineOpens) (f g : Γ(X, U))
          (hU : (U : X.Opens) = X.basicOpen f ⊔ X.basicOpen g),
          (fooSquare2 U f g hU).Condition
            (⊥ : GrothendieckTopology X.smallAffineZariskiSite)
            (DerivedCategory.Plus.ι.obj K) := sorry
