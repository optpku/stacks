module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pullback

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- Quasi-coherent modules on `X` that are flat over `S` along `p : X ⟶ S`. -/
abbrev FlatQCoh {X S : Scheme.{u}} (p : X ⟶ S) : Type (u + 1) :=
  ObjectProperty.FullSubcategory (fun F : QCoh X ↦ Modules.flatOver F.obj p)

namespace FlatQCoh

/-- The inclusion of relatively flat quasi-coherent modules into all quasi-coherent modules. -/
abbrev inclusion {X S : Scheme.{u}} (p : X ⟶ S) : FlatQCoh p ⥤ QCoh X :=
  ObjectProperty.ι (fun F : QCoh X ↦ Modules.flatOver F.obj p)

/-- The underlying module of an object of `FlatQCoh p` is quasi-coherent. -/
instance instIsQuasicoherent {X S : Scheme.{u}} (p : X ⟶ S) (F : FlatQCoh p) :
    F.obj.obj.IsQuasicoherent := sorry

/-- The underlying module of an object of `FlatQCoh p` is flat over the base. -/
instance instFlatOver {X S : Scheme.{u}} (p : X ⟶ S) (F : FlatQCoh p) :
    Modules.flatOver F.obj.obj p := sorry

/-- Pulling a relatively flat quasi-coherent module to a base change preserves relative
flatness over the new base. -/
theorem baseChange_obj_flatOver {X S S' : Scheme.{u}} (p : X ⟶ S) (g : S' ⟶ S)
    (F : FlatQCoh p) :
    Modules.flatOver ((QCoh.pullback (pullback.fst p g)).obj F.obj).obj
      (pullback.snd p g) := sorry

/-- Pullback of relatively flat quasi-coherent modules along a chosen scheme base change. -/
def baseChange {X S S' : Scheme.{u}} (p : X ⟶ S) (g : S' ⟶ S) :
    FlatQCoh p ⥤ FlatQCoh (pullback.snd p g) :=
  ObjectProperty.lift (fun F : QCoh (pullback p g) ↦
      Modules.flatOver F.obj (pullback.snd p g))
    (inclusion p ⋙ QCoh.pullback (pullback.fst p g))
    (baseChange_obj_flatOver p g)

/-- The underlying module of `baseChange p g` is the usual module pullback. -/
theorem baseChange_obj {X S S' : Scheme.{u}} (p : X ⟶ S) (g : S' ⟶ S)
    (F : FlatQCoh p) :
    ((baseChange p g).obj F).obj.obj =
      (Modules.pullback (pullback.fst p g)).obj F.obj.obj := sorry

end FlatQCoh

end AlgebraicGeometry.Scheme
