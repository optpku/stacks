/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Action.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Action.Morphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quasicoherent.Pullback

/-!
# Pullback of equivariant quasi-coherent sheaves

An equivariant morphism `f : X ⟶ Y` of algebraic spaces with `G`-action induces a functor
from quasi-coherent `G`-equivariant sheaves on `Y` to those on `X`, by
`(F, α) ↦ (f* F, (1_G × f)* α)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QCoh.Equivariant

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)

/-- The underlying algebraic-space morphism `1_G × f` induced by an equivariant morphism
`f`. -/
def oneProd {X Y : GroupAlgebraicSpace.Action G} (f : X ⟶ Y) :
    (G.X ⊗ X.X).left ⟶ (G.X ⊗ Y.X).left :=
  (GroupoidAlgebraicSpace.ofActionArrow G f).left

/-- The linearization on a pulled-back equivariant quasi-coherent sheaf, obtained by
pulling back the original linearization along `1_G × f`. -/
def pullbackAlpha {X Y : GroupAlgebraicSpace.Action G} (f : X ⟶ Y)
    (D : Equivariant G Y) :
    (AlgebraicSpace.QCoh.pullback (action G X)).obj
        ((AlgebraicSpace.QCoh.pullback f.hom.left).obj (obj D)) ⟶
      (AlgebraicSpace.QCoh.pullback (projection G X)).obj
        ((AlgebraicSpace.QCoh.pullback f.hom.left).obj (obj D)) :=
  GroupoidAlgebraicSpace.QCoh.pullbackAction (GroupoidAlgebraicSpace.ofActionHom G f) D

/-- Pullback along an equivariant morphism, as a functor on equivariant quasi-coherent
sheaves. -/
def pullback {X Y : GroupAlgebraicSpace.Action G} (f : X ⟶ Y) :
    Equivariant G Y ⥤ Equivariant G X :=
  GroupoidAlgebraicSpace.QCoh.pullback (GroupoidAlgebraicSpace.ofActionHom G f)

/-- The underlying module of equivariant pullback is ordinary quasi-coherent pullback. -/
theorem pullback_obj {X Y : GroupAlgebraicSpace.Action G} (f : X ⟶ Y)
    (D : Equivariant G Y) :
    obj ((pullback G f).obj D) =
      (AlgebraicSpace.QCoh.pullback f.hom.left).obj (obj D) :=
  sorry

/-- The linearization of equivariant pullback is the canonical pullback of the original
linearization along `1_G × f`. -/
theorem pullback_alpha {X Y : GroupAlgebraicSpace.Action G} (f : X ⟶ Y)
    (D : Equivariant G Y) :
    alpha ((pullback G f).obj D) = pullbackAlpha G f D :=
  sorry

/-- The underlying map of equivariant pullback is ordinary quasi-coherent pullback. -/
theorem pullback_map {X Y : GroupAlgebraicSpace.Action G} (f : X ⟶ Y)
    {A B : Equivariant G Y} (a : A ⟶ B) :
    hom ((pullback G f).map a) = (AlgebraicSpace.QCoh.pullback f.hom.left).map (hom a) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.QCoh.Equivariant
