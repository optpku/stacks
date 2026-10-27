/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.SpaceComparison
public import stacks_project.Chap96.Lemma_96_14_2_Restriction
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

noncomputable section

universe u

/- Lemma 96.14.2. Let S be a scheme and let X over (Sch/S)_fppf be a
category fibred in groupoids represented by an algebraic space F. Restriction
of quasi-coherent modules to F_étale is an equivalence, with specified
quasi-inverse π_F^*, compatible with pullback along all morphisms between
such represented categories. -/
@[stacks 0GQD] #check (AlgebraicGeometry.GroupoidsOver.QCoh.restrictEquivalence :
  ∀ {S : Scheme.{u}} {F : AlgebraicSpace S} {X : GroupoidsOver S}
    (e : F.toGroupoids ≌ X), QCoh X ≌ AlgebraicSpace.QCoh F)

#check (AlgebraicGeometry.GroupoidsOver.QCoh.restrictPullbackIso :
  ∀ {S : Scheme.{u}} {F G : AlgebraicSpace S} {X Y : GroupoidsOver S}
    (eX : F.toGroupoids ≌ X) (eY : G.toGroupoids ≌ Y) (f : X ⟶ Y),
    QCoh.pullback f ⋙ QCoh.restrict eX ≅
      QCoh.restrict eY ⋙ AlgebraicSpace.QCoh.pullback
        (moduleComparisonSpaceMorphism f eX eY))

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {F G : AlgebraicSpace S} {X Y : GroupoidsOver S}

/-- The space morphism represented by a morphism of the fibred categories,
with the representing equivalences given first. -/
abbrev recoveredHom (eX : F.toGroupoids ≌ X) (eY : G.toGroupoids ≌ Y)
    (f : X ⟶ Y) : F ⟶ G :=
  moduleComparisonSpaceMorphism f eX eY

namespace QCoh

/-- Pullback compatibility, with an explicit presentation identification retained
in the argument list for existing source presentations. -/
def restrict_pullbackIso (eX : F.toGroupoids ≌ X) (eY : G.toGroupoids ≌ Y)
    (f : X ⟶ Y)
    (α : (f ≫ eY.symm.hom) ≅
      (eX.symm.hom ≫ AlgebraicSpace.toGroupoids.map (recoveredHom eX eY f))) :
    pullback f ⋙ restrict eX ≅
      restrict eY ⋙ AlgebraicSpace.QCoh.pullback (recoveredHom eX eY f) :=
  restrictPullbackIso eX eY f

end QCoh

end AlgebraicGeometry.GroupoidsOver
