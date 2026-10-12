/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Basic
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Map.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Section.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.ToInertia.Construction

/-!
# Underlying detection for relative inertia

This leaf owns the generic lift and strong-cartesianness criteria for relative inertia. The
based-cartesian closure corollaries live in the sibling `Based` leaf.
-/

@[expose] public section

universe u v uS vS uT vT

namespace CategoryTheory

namespace RelativeInertia.Detection

variable {C : Type u} [Category.{v} C]
variable {S : Type uS} [Category.{vS} S]
variable {T : Type uT} [Category.{vT} T]

namespace HomLift

/-- A relative-inertia morphism is a lift for the induced projection exactly when its underlying
arrow is a lift for the source projection. -/
@[stacks 04Z4 "relative inertia underlying lift detection"]
theorem iffProjection
    (F : S ⥤ T) (p : S ⥤ C)
    {X Y : RelativeInertia F} {R Q : C} {f : R ⟶ Q} {φ : X ⟶ Y} :
    (RelativeInertia.projection F p).IsHomLift f φ ↔
      p.IsHomLift f (RelativeInertia.hom φ) := sorry

end HomLift

namespace StronglyCartesian

/-- An underlying strongly cartesian arrow induces a strongly cartesian relative-inertia
morphism over the same displayed base arrow. -/
@[stacks 04Z4 "relative inertia lift from underlying arrow"]
theorem ofUnderlying
    (F : S ⥤ T) (p : S ⥤ C)
    {X Y : RelativeInertia F} {R Q : C} {f : R ⟶ Q} {φ : X ⟶ Y}
    (hφ : p.IsStronglyCartesian f (RelativeInertia.hom φ)) :
    (RelativeInertia.projection F p).IsStronglyCartesian f φ := sorry

/-- For the relative inertia of a cartesian functor with fibred source, strong cartesianness of
an inertia morphism reflects to its underlying source arrow. -/
@[stacks 04Z4 "relative inertia strong-cartesian reflection"]
theorem underlyingOfCartesian
    {p : S ⥤ C} {q : T ⥤ C} [p.IsFibered]
    (F : CartesianBasedFunctor p q)
    {X Y : RelativeInertia F.toFunctor} {R Q : C} {f : R ⟶ Q} {φ : X ⟶ Y}
    (hφ : (RelativeInertia.projection F.toFunctor p).IsStronglyCartesian f φ) :
    p.IsStronglyCartesian f (RelativeInertia.hom φ) := sorry

/-- For the relative inertia of a cartesian functor with fibred source, strong cartesianness is
detected exactly by the underlying source arrow. -/
@[stacks 04Z4 "relative inertia strong-cartesian criterion"]
theorem iffProjection
    {p : S ⥤ C} {q : T ⥤ C} [p.IsFibered]
    (F : CartesianBasedFunctor p q)
    {X Y : RelativeInertia F.toFunctor} {R Q : C} {f : R ⟶ Q} {φ : X ⟶ Y} :
    (RelativeInertia.projection F.toFunctor p).IsStronglyCartesian f φ ↔
      p.IsStronglyCartesian f (RelativeInertia.hom φ) := sorry

/-- For self-inertia over a fibred projection, strong cartesianness reflects to its underlying
arrow. -/
@[stacks 04Z4 "self-inertia strong-cartesian reflection"]
theorem projectionSelf.underlying
    (p : S ⥤ C) [p.IsFibered]
    {X Y : RelativeInertia p} {R Q : C} {f : R ⟶ Q} {φ : X ⟶ Y}
    (hφ : (RelativeInertia.projection p p).IsStronglyCartesian f φ) :
    p.IsStronglyCartesian f (RelativeInertia.hom φ) := sorry

/-- For self-inertia over a fibred projection, a morphism is strongly cartesian exactly when its
underlying arrow is strongly cartesian over the same displayed base arrow. -/
@[stacks 04Z4 "self-inertia strong-cartesian criterion"]
theorem projectionSelf.iff
    (p : S ⥤ C) [p.IsFibered]
    {X Y : RelativeInertia p} {R Q : C} {f : R ⟶ Q} {φ : X ⟶ Y} :
    (RelativeInertia.projection p p).IsStronglyCartesian f φ ↔
      p.IsStronglyCartesian f (RelativeInertia.hom φ) := sorry

end StronglyCartesian

end RelativeInertia.Detection

end CategoryTheory
