module

public import ReasLib.CategoryTheory.Fibered.Cleavage.Basic.Intrinsic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Chosen lifts on standard fibers

This leaf specializes an intrinsic cleavage to standard-fiber objects. It owns the reindexed
object and its chosen strongly cartesian arrow, together with their stable projection and
base-map API.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

open Functor Fiber

namespace Functor.Cleavage

variable {p : S ⥤ C}

/-- A strongly cartesian lift specialized to a standard-fiber object. Unlike the intrinsic
`StronglyCartesianLift`, its displayed base arrow ends at the external fiber index `U`; the
fiber object's endpoint equality is normalized by `reindexLift`. -/
structure FiberLift {U V : C} (p : S ⥤ C) (f : V ⟶ U) (x : Fiber p U) where
  /-- The source of the specialized lift. -/
  source : S
  /-- The specialized cartesian arrow. -/
  hom : source ⟶ x.1
  /-- The source lies over the domain of the displayed base arrow. -/
  sourceObj : p.obj source = V
  /-- The specialized arrow is strongly cartesian over the displayed base arrow. -/
  isStronglyCartesian : p.IsStronglyCartesian f hom

/-- The cleavage lift specialized to an object of the standard fiber.

The endpoint equality carried by `x` is eliminated here, so the resulting lift lies over `f`
itself. The reindexing object and its cartesian arrow are projections of this data owner. -/
@[stacks 02XN "chosen lift specialized to a standard fiber"]
def reindexLift (chi : p.Cleavage) {U V : C} (f : V ⟶ U) (x : Fiber p U) :
    FiberLift p f x :=
  match U, x with
  | _, ⟨_, rfl⟩ =>
      { source := (chi.lift f).source
        hom := (chi.lift f).hom
        sourceObj := (chi.lift f).sourceObj
        isStronglyCartesian := (chi.lift f).isStronglyCartesian }

/-- The source of the chosen lift, bundled as an object of the standard fiber over the domain
of `f`. This owner is shared by the cartesian arrow and the reindexing functor. -/
def reindexObj (chi : p.Cleavage) {U V : C} (f : V ⟶ U)
    (x : Fiber p U) : Fiber p V :=
  ⟨(chi.reindexLift f x).source, (chi.reindexLift f x).sourceObj⟩

/-- The underlying total-category object of `reindexObj` is the source of `reindexLift`. -/
@[simp]
theorem reindexObj.val (chi : p.Cleavage) {U V : C} (f : V ⟶ U) (x : Fiber p U) :
    (chi.reindexObj f x).1 = (chi.reindexLift f x).source := sorry

/-- The projection of a chosen reindexing object is the domain of the base arrow. -/
@[simp]
theorem reindexObj.property (chi : p.Cleavage) {U V : C} (f : V ⟶ U)
    (x : Fiber p U) :
    p.obj (chi.reindexObj f x).1 = V := sorry

/-- The chosen strongly cartesian arrow underlying standard-fiber reindexing. It is derived from
the same intrinsic lift as `reindexObj`. -/
def cartesianHom (chi : p.Cleavage) {U V : C} (f : V ⟶ U)
    (x : Fiber p U) : (chi.reindexObj f x).1 ⟶ x.1 :=
  (chi.reindexLift f x).hom

/-- The standard-fiber cartesian arrow retains the chosen lift's universal property. -/
theorem cartesianHom.isStronglyCartesian (chi : p.Cleavage) {U V : C}
    (f : V ⟶ U) (x : Fiber p U) :
    p.IsStronglyCartesian f (chi.cartesianHom f x) :=
  (chi.reindexLift f x).isStronglyCartesian

/-- The standard-fiber cartesian arrow is a lift of its displayed base arrow. -/
theorem cartesianHom.isHomLift (chi : p.Cleavage) {U V : C} (f : V ⟶ U)
    (x : Fiber p U) :
    p.IsHomLift f (chi.cartesianHom f x) := sorry

/-- The image in the base of the standard-fiber cartesian arrow is the displayed base arrow,
with the endpoint transports carried by the two fiber objects. -/
@[simp]
theorem cartesianHom.map (chi : p.Cleavage) {U V : C} (f : V ⟶ U)
    (x : Fiber p U) :
    p.map (chi.cartesianHom f x) =
      eqToHom (chi.reindexObj f x).2 ≫ f ≫ eqToHom x.2.symm := sorry

end Functor.Cleavage

end CategoryTheory
