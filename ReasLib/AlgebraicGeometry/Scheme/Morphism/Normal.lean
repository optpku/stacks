/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Normal.MorphismProperty
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat

/-!
# Normal morphisms of schemes

This file defines normality at a point of a scheme morphism and the corresponding
global morphism property.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

variable {X Y : Scheme.{u}}

/-- A scheme morphism is normal at `x` when it is flat at `x` and its residue-field
fibre is geometrically normal at the distinguished point `f.asFiber x`. -/
def NormalAt (f : X ⟶ Y) (x : X) : Prop :=
  f.flatAt x ∧
    SchemeOverField.geometricallyNormalAt
      (Over.mk (f.fiberToSpecResidueField (f x))) (f.asFiber x)

/-- A scheme morphism is normal at a point exactly when it is flat there and the
distinguished point of its residue-field fibre is geometrically normal. -/
theorem normalAt_iff (f : X ⟶ Y) (x : X) :
    f.NormalAt x ↔ f.flatAt x ∧
      SchemeOverField.geometricallyNormalAt
        (Over.mk (f.fiberToSpecResidueField (f x))) (f.asFiber x) := sorry

namespace NormalAt

/-- A scheme morphism normal at a point is flat there. -/
theorem flatAt {f : X ⟶ Y} {x : X} (h : f.NormalAt x) :
    f.flatAt x := sorry

/-- At a point where a scheme morphism is normal, the distinguished point of its
residue-field fibre is geometrically normal. -/
theorem geometricallyNormalAt {f : X ⟶ Y} {x : X} (h : f.NormalAt x) :
    SchemeOverField.geometricallyNormalAt
      (Over.mk (f.fiberToSpecResidueField (f x))) (f.asFiber x) := sorry

end NormalAt
end Scheme.Hom

/-- A scheme morphism is normal when it is normal at every point of its source. -/
class Normal {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where
  /-- A normal morphism is normal at each source point. -/
  normalAt : ∀ x : X, f.NormalAt x

/-- A scheme morphism is normal exactly when it is normal at every point of its source. -/
theorem normal_iff_forall_normalAt {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Normal f ↔ ∀ x : X, f.NormalAt x := sorry

namespace Normal

variable {X Y : Scheme.{u}}

/-- Every normal scheme morphism is flat. -/
instance instFlat (f : X ⟶ Y) [Normal f] : Flat f := sorry

end Normal
end AlgebraicGeometry
