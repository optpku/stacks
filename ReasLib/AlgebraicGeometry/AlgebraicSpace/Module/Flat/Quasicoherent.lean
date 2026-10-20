/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange

/-!
# Relatively flat quasi-coherent modules on algebraic spaces

Quasi-coherent modules on an algebraic space that are flat over a given
morphism, together with pullback of such modules along a chosen base change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Quasi-coherent modules on `X` that are flat over `Y` along `p : X ⟶ Y`. -/
abbrev FlatQCoh {S : Scheme.{u}} {X Y : AlgebraicSpace S} (p : X ⟶ Y) : Type (u + 1) :=
  ObjectProperty.FullSubcategory (fun F : QCoh X ↦ Modules.flatOver F.obj p)

namespace FlatQCoh

/-- The inclusion of relatively flat quasi-coherent modules into all quasi-coherent modules. -/
abbrev inclusion {S : Scheme.{u}} {X Y : AlgebraicSpace S} (p : X ⟶ Y) :
    FlatQCoh p ⥤ QCoh X :=
  ObjectProperty.ι (fun F : QCoh X ↦ Modules.flatOver F.obj p)

/-- The underlying module of an object of `FlatQCoh p` is quasi-coherent. -/
instance instIsQuasicoherent {S : Scheme.{u}} {X Y : AlgebraicSpace S} (p : X ⟶ Y)
    (F : FlatQCoh p) : F.obj.obj.IsQuasicoherent := sorry

/-- The underlying module of an object of `FlatQCoh p` is flat over the base. -/
theorem obj_flatOver {S : Scheme.{u}} {X Y : AlgebraicSpace S} (p : X ⟶ Y)
    (F : FlatQCoh p) : Modules.flatOver F.obj.obj p := sorry

/-- Pulling a relatively flat quasi-coherent module to a base change preserves relative
flatness over the new base. -/
theorem baseChange_obj_flatOver {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S}
    (p : X ⟶ Y) (g : Y' ⟶ Y) (F : FlatQCoh p) :
    Modules.flatOver ((QCoh.pullback (pullback.fst p g)).obj F.obj).obj
      (pullback.snd p g) := sorry

/-- Pullback of relatively flat quasi-coherent modules along a chosen algebraic-space
base change. -/
def baseChange {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S} (p : X ⟶ Y) (g : Y' ⟶ Y) :
    FlatQCoh p ⥤ FlatQCoh (pullback.snd p g) :=
  ObjectProperty.lift (fun F : QCoh (pullback p g) ↦
      Modules.flatOver F.obj (pullback.snd p g))
    (inclusion p ⋙ QCoh.pullback (pullback.fst p g))
    (baseChange_obj_flatOver p g)

/-- The underlying module of `baseChange p g` is the usual module pullback. -/
theorem baseChange_obj {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S}
    (p : X ⟶ Y) (g : Y' ⟶ Y) (F : FlatQCoh p) :
    ((baseChange p g).obj F).obj.obj =
      (Modules.pullback (pullback.fst p g)).obj F.obj.obj := sorry

end FlatQCoh

end AlgebraicGeometry.AlgebraicSpace
