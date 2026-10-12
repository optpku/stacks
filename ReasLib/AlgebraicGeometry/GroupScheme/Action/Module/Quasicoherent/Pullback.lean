/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupScheme.Action.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Action.Morphism
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Module.Quasicoherent.Pullback

/-!
# Pullback of equivariant quasi-coherent modules

This module specializes pullback along a morphism of groupoid schemes to an equivariant
morphism between schemes carrying an action of a fixed group scheme.
-/

@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.QCoh.Equivariant

/-- The underlying scheme morphism `1_G × f` induced by an equivariant morphism `f`. -/
def oneProd {S : Scheme.{u}} (G : Grp (Over S)) {X Y : GroupScheme.Action G}
    (f : Y ⟶ X) : (G.X ⊗ Y.X).left ⟶ (G.X ⊗ X.X).left :=
  (GroupoidScheme.ofActionArrow G f).left

/-- The linearization on a pulled-back equivariant quasi-coherent module, obtained by
pulling back the original linearization along `1_G × f` and the canonical source and target
comparisons. -/
noncomputable def pullbackAlpha {S : Scheme.{u}} (G : Grp (Over S))
    {X Y : GroupScheme.Action G} (f : Y ⟶ X) (D : QCoh.Equivariant G X) :
    (QCoh.pullback (action G Y)).obj
        ((QCoh.pullback f.hom.left).obj (QCoh.Equivariant.obj D)) ⟶
      (QCoh.pullback (projection G Y)).obj
        ((QCoh.pullback f.hom.left).obj (QCoh.Equivariant.obj D)) :=
  GroupoidScheme.QCoh.pullbackAction (GroupoidScheme.ofActionHom G f) D

/-- Pullback along an equivariant morphism, as a functor on equivariant quasi-coherent
modules. -/
noncomputable def pullback {S : Scheme.{u}} (G : Grp (Over S))
    {X Y : GroupScheme.Action G} (f : Y ⟶ X) :
    QCoh.Equivariant G X ⥤ QCoh.Equivariant G Y :=
  GroupoidScheme.QCoh.pullback (GroupoidScheme.ofActionHom G f)

/-- The underlying module of equivariant pullback is ordinary quasi-coherent pullback. -/
theorem pullback_obj {S : Scheme.{u}} (G : Grp (Over S))
    {X Y : GroupScheme.Action G} (f : Y ⟶ X) (D : QCoh.Equivariant G X) :
    QCoh.Equivariant.obj ((pullback G f).obj D) =
      (QCoh.pullback f.hom.left).obj (QCoh.Equivariant.obj D) := sorry

/-- The linearization of equivariant pullback is the canonical pullback of the original
linearization along `1_G × f`. -/
theorem pullback_alpha {S : Scheme.{u}} (G : Grp (Over S))
    {X Y : GroupScheme.Action G} (f : Y ⟶ X) (D : QCoh.Equivariant G X) :
    QCoh.Equivariant.alpha ((pullback G f).obj D) = pullbackAlpha G f D := sorry

/-- The underlying map of equivariant pullback is ordinary quasi-coherent pullback. -/
theorem pullback_map {S : Scheme.{u}} (G : Grp (Over S))
    {X Y : GroupScheme.Action G} (f : Y ⟶ X) {D E : QCoh.Equivariant G X}
    (a : D ⟶ E) :
    QCoh.Equivariant.hom ((pullback G f).map a) =
      (QCoh.pullback f.hom.left).map (QCoh.Equivariant.hom a) := sorry

end AlgebraicGeometry.Scheme.QCoh.Equivariant
