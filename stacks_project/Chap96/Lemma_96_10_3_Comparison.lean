/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.MorphismComparison
public import stacks_project.Chap96.«96_10_3_3_Comparison»

/-!
# Comparison square of ringed topoi for a morphism of representing algebraic spaces

A 1-morphism `f : X ⟶ Y` of categories fibred in groupoids over `(Sch/S)_fppf`,
with `X` and `Y` represented by algebraic spaces `F` and `G`, induces a
commutative square of ringed topoi with edges `f`, `π_F`, `π_G`, and `f_small`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open Opposite FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The morphism of algebraic spaces induced by a 1-morphism of categories fibred
in groupoids presented by `F` and `G`. -/
abbrev inducedHom {F G : AlgebraicSpace S} {X Y : GroupoidsOver S}
    (eX : F.toGroupoids ≌ X) (eY : G.toGroupoids ≌ Y) (f : X ⟶ Y) : F ⟶ G :=
  AlgebraicSpace.toGroupoids.recover eX.symm eY.symm f

/-- `inducedHom eX eY f` is recovery of `f` along `eX.symm` and `eY.symm`. -/
theorem inducedHom_eq {F G : AlgebraicSpace S} {X Y : GroupoidsOver S}
    (eX : F.toGroupoids ≌ X) (eY : G.toGroupoids ≌ Y) (f : X ⟶ Y) :
    inducedHom eX eY f = AlgebraicSpace.toGroupoids.recover eX.symm eY.symm f :=
  rfl

/-- The cartesian total functor agrees definitionally with `toFunctor`. -/
def cartesianToFunctorIso {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    (toCartesianBasedFunctor h).toFunctor ≅ toFunctor h :=
  Iso.refl _

variable {X Y : GroupoidsOver S} {F G : AlgebraicSpace S}
variable (eX : F.toGroupoids ≌ X) (eY : G.toGroupoids ≌ Y) (f : X ⟶ Y)
variable (α : (f ≫ eY.symm.hom) ≅
    (eX.symm.hom ≫ AlgebraicSpace.toGroupoids.map (inducedHom eX eY f)))

/-- Transport of a presentation isomorphism through the representing equivalences
identifies the represented morphism with the induced morphism of algebraic spaces. -/
@[expose] def presentedTwoCell :
    eX.hom ≫ f ≅
      AlgebraicSpace.toGroupoids.map (inducedHom eX eY f) ≫ eY.hom :=
  presentationTwoIso eX eY f α

variable [HasSheafify (AlgebraicSpace.smallEtaleTopology F) (Type u)]
variable [HasSheafify (AlgebraicSpace.smallEtaleTopology G) (Type u)]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor F X eX).op.HasLeftKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite G)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor G Y eY).op.HasLeftKanExtension P]

#check (AlgebraicGeometry.GroupoidsOver.compareMorphism eX eY f α :
    RingedSite.ToposHom.CommSquare (etaleRingedSite X) (etaleRingedSite Y)
      (AlgebraicSpace.ringedSite F) (AlgebraicSpace.ringedSite G))

end AlgebraicGeometry.GroupoidsOver
