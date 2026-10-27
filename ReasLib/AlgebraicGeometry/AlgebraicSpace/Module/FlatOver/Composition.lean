/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.FaithfullyFlat.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.Stalk
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# Composition and descent of relative flatness

Relative flatness of quasi-coherent modules on algebraic spaces is transitive along a
morphism flat at the image point. A nonzero field-valued fiber or a faithfully flat
geometric stalk gives converse criteria for flatness of the intermediate morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}

/-- A quasi-coherent module flat at a point over an intermediate algebraic space is flat
over the final target if the intermediate morphism is flat at the image point. -/
theorem flatOverAt_trans (F : X.Modules) [F.IsQuasicoherent] (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : Points X) (hF : flatOverAt F f x) (hY : FlatAt g (Points.map f x)) :
    flatOverAt F (f ≫ g) x := sorry

/-- If a quasi-coherent module is flat at a point over both the intermediate and final
targets and its pullback to a field-valued representative is nonzero, the intermediate
morphism is flat at the image point. -/
theorem flatAt_of_flatOverAt_of_pullback_ne_zero (F : X.Modules) [F.IsQuasicoherent]
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : Points X) (p : FieldValuedPoint X) (hp : Points.mk p = x)
    (hXY : flatOverAt F f x) (hne : ¬ IsZero ((pullback p.hom).obj F))
    (hXZ : flatOverAt F (f ≫ g) x) :
    FlatAt g (Points.map f x) := sorry

/-- If a quasi-coherent module has a faithfully flat geometric stalk over the intermediate
étale local ring and is relatively flat over the final target, the intermediate morphism
is flat at the image point. -/
theorem flatAt_of_stalk_faithfullyFlatAlong (F : X.Modules) [F.IsQuasicoherent]
    (f : X ⟶ Y) (g : Y ⟶ Z) (xbar : GeometricPoint X) (x : Points X) (hx : xbar.liesOver x)
    (hff : Module.FaithfullyFlatAlong (etaleLocalRingMap f xbar) (stalkModuleCat xbar F))
    (hXZ : flatOverAt F (f ≫ g) x) :
    FlatAt g (Points.map f x) := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
