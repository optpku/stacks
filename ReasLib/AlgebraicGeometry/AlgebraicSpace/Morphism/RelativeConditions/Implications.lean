/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeConditions
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.VeryReasonable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation

/-!
# Implications among relative conditions

Representable and quasi-separated morphisms of algebraic spaces are very reasonable.
Very reasonable morphisms are reasonable, reasonable morphisms are decent, and decent
morphisms have property (β).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace VeryReasonable

/-- A representable morphism of algebraic spaces over a scheme is very reasonable. -/
theorem of_relativelyRepresentable {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f) : VeryReasonable f :=
  sorry

/-- A quasi-separated morphism of algebraic spaces over a scheme is very reasonable. -/
@[instance 900]
instance of_quasiSeparated {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiSeparated f] : VeryReasonable f :=
  sorry

end VeryReasonable

namespace Reasonable

/-- A very reasonable morphism of algebraic spaces over a scheme is reasonable. -/
@[instance 900]
instance of_veryReasonable {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [VeryReasonable f] : Reasonable f :=
  sorry

end Reasonable

namespace Decent

/-- A reasonable morphism of algebraic spaces over a scheme is decent. -/
@[instance 900]
instance of_reasonable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Reasonable f] : Decent f :=
  sorry

end Decent

namespace PropertyBeta

/-- A decent morphism of algebraic spaces over a scheme has property (β). -/
@[instance 900]
instance of_decent {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Decent f] : PropertyBeta f :=
  sorry

end PropertyBeta

end AlgebraicGeometry.AlgebraicSpace
