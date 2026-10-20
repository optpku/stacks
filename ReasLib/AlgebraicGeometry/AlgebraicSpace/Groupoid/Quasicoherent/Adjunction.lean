/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quasicoherent.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage

/-!
# Pullback–pushforward adjunction on equivariant quasi-coherent modules

Equivariant pullback is left adjoint to equivariant pushforward, obtained by lifting
the module-level adjunction along the object component.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Limits hiding pullback

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

namespace QCoh

variable {S : Scheme.{u}} {B : AlgebraicSpace S}
variable {G H : GroupoidAlgebraicSpace B}

/-- The underlying quasi-coherent morphism of the adjunction unit, obtained from the module
unit along the object component. -/
def adjunctionUnitHom (f : Hom G H)
    [AlgebraicSpace.QuasiCompact f.obj.left] [AlgebraicSpace.QuasiSeparated f.obj.left]
    [AlgebraicSpace.Flat H.s.left] [AlgebraicSpace.Flat H.t.left]
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left) (A : H.QCoh) :
    A.obj ⟶ ((pushforward f h_target).obj ((pullback f).obj A)).obj :=
  (AlgebraicSpace.quasiCoherentModuleProperty H.U.left).homMk
    ((AlgebraicSpace.Modules.pullbackPushforwardAdjunction f.obj.left).unit.app A.obj.obj)

/-- The module-level unit is compatible with equivariance. -/
theorem adjunctionUnit_compatibility (f : Hom G H)
    [AlgebraicSpace.QuasiCompact f.obj.left] [AlgebraicSpace.QuasiSeparated f.obj.left]
    [AlgebraicSpace.Flat H.s.left] [AlgebraicSpace.Flat H.t.left]
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left) (A : H.QCoh) :
    (AlgebraicSpace.QCoh.pullback H.t.left).map (adjunctionUnitHom f h_target A) ≫
        ((pushforward f h_target).obj ((pullback f).obj A)).action =
      A.action ≫
        (AlgebraicSpace.QCoh.pullback H.s.left).map (adjunctionUnitHom f h_target A) :=
  sorry

/-- The adjunction unit on an equivariant quasi-coherent module. -/
def adjunctionUnitApp (f : Hom G H)
    [AlgebraicSpace.QuasiCompact f.obj.left] [AlgebraicSpace.QuasiSeparated f.obj.left]
    [AlgebraicSpace.Flat H.s.left] [AlgebraicSpace.Flat H.t.left]
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left) (A : H.QCoh) :
    A ⟶ (pushforward f h_target).obj ((pullback f).obj A) :=
  System.Hom.of (adjunctionUnitHom f h_target A) (adjunctionUnit_compatibility f h_target A)

/-- The adjunction unit is natural. -/
theorem adjunctionUnit_naturality (f : Hom G H)
    [AlgebraicSpace.QuasiCompact f.obj.left] [AlgebraicSpace.QuasiSeparated f.obj.left]
    [AlgebraicSpace.Flat H.s.left] [AlgebraicSpace.Flat H.t.left]
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left)
    {M N : H.QCoh} (a : M ⟶ N) :
    a ≫ adjunctionUnitApp f h_target N =
      adjunctionUnitApp f h_target M ≫
        (pushforward f h_target).map ((pullback f).map a) :=
  sorry

/-- The unit of `pullback f ⊣ pushforward f h_target`. -/
def adjunctionUnit (f : Hom G H)
    [AlgebraicSpace.QuasiCompact f.obj.left] [AlgebraicSpace.QuasiSeparated f.obj.left]
    [AlgebraicSpace.Flat H.s.left] [AlgebraicSpace.Flat H.t.left]
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left) :
    𝟭 H.QCoh ⟶ pullback f ⋙ pushforward f h_target where
  app := adjunctionUnitApp f h_target
  naturality := fun _ _ a ↦ adjunctionUnit_naturality f h_target a

/-- The underlying module morphism of the adjunction unit is the module-level unit along the
object component. -/
theorem adjunctionUnit_hom (f : Hom G H)
    [AlgebraicSpace.QuasiCompact f.obj.left] [AlgebraicSpace.QuasiSeparated f.obj.left]
    [AlgebraicSpace.Flat H.s.left] [AlgebraicSpace.Flat H.t.left]
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left) (A : H.QCoh) :
    (hom ((adjunctionUnit f h_target).app A)).hom =
      (AlgebraicSpace.Modules.pullbackPushforwardAdjunction f.obj.left).unit.app A.obj.obj :=
  sorry

/-- The underlying quasi-coherent morphism of the adjunction counit, obtained from the module
counit along the object component. -/
def adjunctionCounitHom (f : Hom G H)
    [AlgebraicSpace.QuasiCompact f.obj.left] [AlgebraicSpace.QuasiSeparated f.obj.left]
    [AlgebraicSpace.Flat H.s.left] [AlgebraicSpace.Flat H.t.left]
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left) (A : G.QCoh) :
    ((pullback f).obj ((pushforward f h_target).obj A)).obj ⟶ A.obj :=
  (AlgebraicSpace.quasiCoherentModuleProperty G.U.left).homMk
    ((AlgebraicSpace.Modules.pullbackPushforwardAdjunction f.obj.left).counit.app A.obj.obj)

/-- The module-level counit is compatible with equivariance. -/
theorem adjunctionCounit_compatibility (f : Hom G H)
    [AlgebraicSpace.QuasiCompact f.obj.left] [AlgebraicSpace.QuasiSeparated f.obj.left]
    [AlgebraicSpace.Flat H.s.left] [AlgebraicSpace.Flat H.t.left]
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left) (A : G.QCoh) :
    (AlgebraicSpace.QCoh.pullback G.t.left).map (adjunctionCounitHom f h_target A) ≫ A.action =
      ((pullback f).obj ((pushforward f h_target).obj A)).action ≫
        (AlgebraicSpace.QCoh.pullback G.s.left).map (adjunctionCounitHom f h_target A) :=
  sorry

/-- The adjunction counit on an equivariant quasi-coherent module. -/
def adjunctionCounitApp (f : Hom G H)
    [AlgebraicSpace.QuasiCompact f.obj.left] [AlgebraicSpace.QuasiSeparated f.obj.left]
    [AlgebraicSpace.Flat H.s.left] [AlgebraicSpace.Flat H.t.left]
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left) (A : G.QCoh) :
    (pullback f).obj ((pushforward f h_target).obj A) ⟶ A :=
  System.Hom.of (adjunctionCounitHom f h_target A) (adjunctionCounit_compatibility f h_target A)

/-- The adjunction counit is natural. -/
theorem adjunctionCounit_naturality (f : Hom G H)
    [AlgebraicSpace.QuasiCompact f.obj.left] [AlgebraicSpace.QuasiSeparated f.obj.left]
    [AlgebraicSpace.Flat H.s.left] [AlgebraicSpace.Flat H.t.left]
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left)
    {M N : G.QCoh} (a : M ⟶ N) :
    (pullback f).map ((pushforward f h_target).map a) ≫ adjunctionCounitApp f h_target N =
      adjunctionCounitApp f h_target M ≫ a :=
  sorry

/-- The counit of `pullback f ⊣ pushforward f h_target`. -/
def adjunctionCounit (f : Hom G H)
    [AlgebraicSpace.QuasiCompact f.obj.left] [AlgebraicSpace.QuasiSeparated f.obj.left]
    [AlgebraicSpace.Flat H.s.left] [AlgebraicSpace.Flat H.t.left]
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left) :
    pushforward f h_target ⋙ pullback f ⟶ 𝟭 G.QCoh where
  app := adjunctionCounitApp f h_target
  naturality := fun _ _ a ↦ adjunctionCounit_naturality f h_target a

/-- The underlying module morphism of the adjunction counit is the module-level counit along
the object component. -/
theorem adjunctionCounit_hom (f : Hom G H)
    [AlgebraicSpace.QuasiCompact f.obj.left] [AlgebraicSpace.QuasiSeparated f.obj.left]
    [AlgebraicSpace.Flat H.s.left] [AlgebraicSpace.Flat H.t.left]
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left) (A : G.QCoh) :
    (hom ((adjunctionCounit f h_target).app A)).hom =
      (AlgebraicSpace.Modules.pullbackPushforwardAdjunction f.obj.left).counit.app A.obj.obj :=
  sorry

/-- The left triangle identity for the equivariant pullback–pushforward adjunction. -/
theorem adjunction_left_triangle (f : Hom G H)
    [AlgebraicSpace.QuasiCompact f.obj.left] [AlgebraicSpace.QuasiSeparated f.obj.left]
    [AlgebraicSpace.Flat H.s.left] [AlgebraicSpace.Flat H.t.left]
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left) (A : H.QCoh) :
    (pullback f).map ((adjunctionUnit f h_target).app A) ≫
        (adjunctionCounit f h_target).app ((pullback f).obj A) =
      𝟙 ((pullback f).obj A) :=
  sorry

/-- The right triangle identity for the equivariant pullback–pushforward adjunction. -/
theorem adjunction_right_triangle (f : Hom G H)
    [AlgebraicSpace.QuasiCompact f.obj.left] [AlgebraicSpace.QuasiSeparated f.obj.left]
    [AlgebraicSpace.Flat H.s.left] [AlgebraicSpace.Flat H.t.left]
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left) (A : G.QCoh) :
    (adjunctionUnit f h_target).app ((pushforward f h_target).obj A) ≫
        (pushforward f h_target).map ((adjunctionCounit f h_target).app A) =
      𝟙 ((pushforward f h_target).obj A) :=
  sorry

/-- Pullback along a morphism of groupoids in algebraic spaces with quasi-compact and
quasi-separated object map and cartesian target square is left adjoint to equivariant
pushforward when the source and target maps of the target groupoid are flat. -/
def pullbackPushforwardAdjunction (f : Hom G H)
    [AlgebraicSpace.QuasiCompact f.obj.left] [AlgebraicSpace.QuasiSeparated f.obj.left]
    [AlgebraicSpace.Flat H.s.left] [AlgebraicSpace.Flat H.t.left]
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left) :
    pullback f ⊣ pushforward f h_target where
  unit := adjunctionUnit f h_target
  counit := adjunctionCounit f h_target
  left_triangle_components := adjunction_left_triangle f h_target
  right_triangle_components := adjunction_right_triangle f h_target

end QCoh

end AlgebraicGeometry.GroupoidAlgebraicSpace
