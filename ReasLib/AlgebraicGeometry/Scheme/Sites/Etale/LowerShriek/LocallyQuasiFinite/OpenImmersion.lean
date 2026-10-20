/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteSupport.OpenImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite.Properties
public import ReasLib.CategoryTheory.Sites.Topos.Continuous

/-!
# Open-immersion covariance of locally quasi-finite lower shriek

Sheafification of finite-support covariance gives covariance of lower shriek.
Its stalk maps are induced by composition of geometric lifts with the open immersion.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint
open Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X' X Y : Scheme.{u}} (j : X' ⟶ X) (f : X ⟶ Y)
variable [IsOpenImmersion j] [LocallyQuasiFinite f]

/-- Compact-support direct image is unchanged when the scheme morphism is
replaced by an equal morphism. -/
def lowerShriekCongr {X Y : Scheme.{u}} {g h : X ⟶ Y}
    [LocallyQuasiFinite g] [LocallyQuasiFinite h]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}] (e : g = h) :
    lowerShriek g ≅ lowerShriek h :=
  eqToIso (e ▸ rfl)

section SheafCovariance

variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]

/-- Canonical covariance `f'_!(F|_{X'}) ⟶ f_! F` of compact-support direct
images along an open immersion of the source, obtained by sheafifying
`lowerShriekPresheafOpenImmersion`. -/
def lowerShriekOpenImmersion :
    etaleRestrictionSheaf j AddCommGrpCat.{u} ⋙ lowerShriek (j ≫ f) ⟶
      lowerShriek f :=
  whiskerRight (lowerShriekPresheafOpenImmersion j f)
    (presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u})

/-- The sheaf covariance is the sheafification of the presheaf covariance. -/
theorem lowerShriekOpenImmersion_eq :
    lowerShriekOpenImmersion j f =
      whiskerRight (lowerShriekPresheafOpenImmersion j f)
        (presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :=
  rfl

/-- Covariance along nested open immersions `X'' ⟶ X' ⟶ X` is the composite of
the two sheaf covariance maps. -/
theorem lowerShriekOpenImmersion_comp {X'' : Scheme.{u}} (j' : X'' ⟶ X')
    [IsOpenImmersion j'] :
    whiskerLeft (etaleRestrictionSheaf j AddCommGrpCat.{u})
          (lowerShriekOpenImmersion j' (j ≫ f)) ≫
        lowerShriekOpenImmersion j f =
      whiskerRight (etaleAbelianRestrictionSheafCompIso j j').hom
          (lowerShriek (j' ≫ j ≫ f)) ≫
        whiskerLeft (etaleRestrictionSheaf (j' ≫ j) AddCommGrpCat.{u})
          (lowerShriekCongr (Category.assoc j' j f).symm).hom ≫
          lowerShriekOpenImmersion (j' ≫ j) f :=
  sorry

/-- Covariance of locally quasi-finite lower shriek along the open immersion of
a Zariski open subscheme. -/
abbrev lowerShriekOpenImmersion_opens {X Y : Scheme.{u}} (U : X.Opens)
    (f : X ⟶ Y) [LocallyQuasiFinite f]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}] :
    etaleRestrictionSheaf U.ι AddCommGrpCat.{u} ⋙ lowerShriek (U.ι ≫ f) ⟶
      lowerShriek f :=
  lowerShriekOpenImmersion U.ι f

end SheafCovariance

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator must expose this private implementation to the public stalk maps.
set_option backward.privateInPublic true in
/-- Composing a geometric lift with an open immersion gives a geometric lift
along the original morphism. -/
private def fiberOpenImmersion (ybar : GeometricPoint Y)
    (x' : Fiber (j ≫ f) ybar) : Fiber f ybar :=
  Fiber.of (x'.lift ≫ j) (by simpa only [Category.assoc] using x'.fac)

section Stalks

variable (ybar : GeometricPoint Y)

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator must expose this private implementation to the public stalk maps.
set_option backward.privateInPublic true in
/-- A lift of a geometric point of `X'` over `ȳ` to an étale `X'`-scheme is the
same lift of the image point of `X` to the restricted étale `X`-scheme. -/
private def restrictionFiberElement (x' : Fiber (j ≫ f) ybar) (U : X'.Etale)
    (φ : (toSmallEtalePoint x'.point).fiber.obj U) :
    (toSmallEtalePoint (fiberOpenImmersion j f ybar x').point).fiber.obj
      ((etaleRestriction j).obj U) :=
  (CategoryTheory.Over.homMk φ.left (by
      change φ.left ≫ (U.hom ≫ j) = x'.lift ≫ j
      rw [← Category.assoc]
      exact congrArg (fun g ↦ g ≫ j) φ.w) :
    (toSmallEtalePoint (fiberOpenImmersion j f ybar x').point).fiber.obj
      ((etaleRestriction j).obj U))

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator requires access to the complete private geometric-lift transports.
set_option backward.privateInPublic true in
/-- Identification of the stalk of `F|_{X'}` at a geometric point of `X'` over
`ȳ` with the stalk of `F` at the image geometric point of `X`. -/
def restrictionSheafFiber (x' : Fiber (j ≫ f) ybar)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (toSmallEtalePoint x'.point).sheafFiber.obj
        ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F) ⟶
      (toSmallEtalePoint
          (fiberOpenImmersion j f ybar x').point).sheafFiber.obj F :=
  (toSmallEtalePoint x'.point).presheafFiberDesc
    (fun U φ ↦
      ((etaleRestriction j).sheafPushforwardContinuousObjObjIso
        (J := X'.smallEtaleTopology) (K := X.smallEtaleTopology)
        AddCommGrpCat.{u} F U).hom ≫
        (toSmallEtalePoint (fiberOpenImmersion j f ybar x').point).toPresheafFiber
          ((etaleRestriction j).obj U) (restrictionFiberElement j f ybar x' U φ) F.1)
    sorry

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator requires access to the complete private geometric-lift transports.
set_option backward.privateInPublic true in
/-- Inclusion of fibrewise stalk coproducts along an open immersion of the
source, reindexing geometric points of `X'` over `ȳ` to geometric points of `X`
over `ȳ`. -/
def abelianStalkCoproductOpenImmersion :
    etaleRestrictionSheaf j AddCommGrpCat.{u} ⋙ abelianStalkCoproduct (j ≫ f) ybar ⟶
      abelianStalkCoproduct f ybar where
  app F :=
    Sigma.map' (fiberOpenImmersion j f ybar) fun x' ↦
      restrictionSheafFiber j f ybar x' F
  naturality := sorry

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator requires access to the complete private geometric-lift transports.
set_option backward.privateInPublic true in
/-- Evaluating the fibre-coproduct covariance recovers `Sigma.map'` of the
stalk identifications. -/
theorem abelianStalkCoproductOpenImmersion_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (abelianStalkCoproductOpenImmersion j f ybar).app F =
      Sigma.map' (fiberOpenImmersion j f ybar) fun x' ↦
        restrictionSheafFiber j f ybar x' F :=
  rfl

variable [LocallyOfFiniteType f]

/-- Presheaf covariance commutes with the canonical coproduct description of stalks. -/
theorem lowerShriekPresheafOpenImmersion_stalk
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    CommSq
      ((toSmallEtalePoint ybar).presheafFiber.map
        ((lowerShriekPresheafOpenImmersion j f).app F))
      ((lowerShriekPresheafStalkIso (j ≫ f) ybar).hom.app
        ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F))
      ((lowerShriekPresheafStalkIso f ybar).hom.app F)
      ((abelianStalkCoproductOpenImmersion j f ybar).app F) :=
  sorry

variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]

/-- Sheaf covariance commutes with the canonical coproduct description of stalks. -/
theorem lowerShriekOpenImmersion_stalk
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    CommSq
      ((toSmallEtalePoint ybar).sheafFiber.map
        ((lowerShriekOpenImmersion j f).app F))
      ((lowerShriekStalkIso (j ≫ f) ybar).hom.app
        ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F))
      ((lowerShriekStalkIso f ybar).hom.app F)
      ((abelianStalkCoproductOpenImmersion j f ybar).app F) :=
  sorry


end Stalks

variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]

/-- The covariance comparison `f'_! F' ⟶ f_! F` is a monomorphism. -/
instance lowerShriekOpenImmersion_app_mono [LocallyOfFiniteType f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    Mono ((lowerShriekOpenImmersion j f).app F) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end

end
