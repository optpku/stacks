/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.Composition
import StacksCheckRecall

/-!
# Transitivity and converse criteria for relative flatness of modules

The three criteria concern relative flatness of a quasi-coherent module on algebraic spaces,
with nonzero field-valued pullback and faithfully flat geometric stalk hypotheses for the
converse implications.
-/

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Lemma 67.31.4 (1): Relative flatness is transitive along a morphism flat at the image
point. -/
@[stacks 05VX] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.flatOverAt_trans :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (F : X.Modules) [F.IsQuasicoherent]
      (f : X ⟶ Y) (g : Y ⟶ Z) (x : Points X)
      (hF : flatOverAt F f x) (hY : FlatAt g (Points.map f x)),
      flatOverAt F (f ≫ g) x)

/- Lemma 67.31.4 (2): Relative flatness over both targets and a nonzero pullback to a
field-valued representative imply flatness of the intermediate morphism. -/
@[stacks 05VX] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.flatAt_of_flatOverAt_of_pullback_ne_zero :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (F : X.Modules) [F.IsQuasicoherent]
      (f : X ⟶ Y) (g : Y ⟶ Z) (x : Points X) (p : FieldValuedPoint X) (hp : Points.mk p = x)
      (hXY : flatOverAt F f x) (hne : ¬ IsZero ((Modules.pullback p.hom).obj F))
      (hXZ : flatOverAt F (f ≫ g) x),
      FlatAt g (Points.map f x))

/- Lemma 67.31.4 (3): A faithfully flat geometric stalk over the intermediate étale local
ring and relative flatness over the final target imply flatness of the intermediate morphism. -/
@[stacks 05VX] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.flatAt_of_stalk_faithfullyFlatAlong :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (F : X.Modules) [F.IsQuasicoherent]
      (f : X ⟶ Y) (g : Y ⟶ Z) (xbar : GeometricPoint X) (x : Points X) (hx : xbar.liesOver x)
      (hff : Module.FaithfullyFlatAlong (etaleLocalRingMap f xbar) (stalkModuleCat xbar F))
      (hXZ : flatOverAt F (f ≫ g) x),
      FlatAt g (Points.map f x))
