/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.ObjectProperty.Localization.Resolution.Right.Map
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Resolution.Right.Monotonicity
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Monotonicity of Maps of Property-Indexed Right Resolutions

Weakening the object and comparison properties of right resolutions also transports maps over
arbitrary target morphisms.  The transport leaves the ambient morphism unchanged and is compatible
with the identity, composition, and reindexing operations.
-/

@[expose] public section

universe v u

namespace CategoryTheory.ObjectProperty.RightResolution.mapOfLE

variable {D : Type u} [Category.{v} D]
  {P Q : ObjectProperty D} {S T : MorphismProperty D}

/-- The image of a right-resolution map under weaker model and comparison properties satisfies
the required comparison square. -/
theorem map_naturality (hP : P ≤ Q) (hS : S ≤ T)
    {X Y : D} {f : X ⟶ Y} {R : RightResolution P S X} {R' : RightResolution P S Y}
    (m : Map f R R') :
    (R.mapOfLE hP hS).comparison ≫
        Q.ι.map ((P.ιOfLE hP).map m.modelHom) =
      f ≫ (R'.mapOfLE hP hS).comparison := sorry

/-- Transport a map of right resolutions after weakening the model and comparison properties. -/
@[stacks 0GSL "monotonicity of maps of right resolutions"]
def map (hP : P ≤ Q) (hS : S ≤ T)
    {X Y : D} {f : X ⟶ Y} {R : RightResolution P S X} {R' : RightResolution P S Y}
    (m : Map f R R') :
    Map f (R.mapOfLE hP hS) (R'.mapOfLE hP hS) :=
  Map.mk ((P.ιOfLE hP).map m.modelHom) (map_naturality hP hS m)

/-- Transporting a right-resolution map applies `ObjectProperty.ιOfLE` to its bundled model
morphism. -/
@[simp]
theorem map_modelHom (hP : P ≤ Q) (hS : S ≤ T)
    {X Y : D} {f : X ⟶ Y} {R : RightResolution P S X} {R' : RightResolution P S Y}
    (m : Map f R R') :
    (map hP hS m).modelHom = (P.ιOfLE hP).map m.modelHom := sorry

/-- Transporting a right-resolution map retains its ambient morphism. -/
@[simp]
theorem map_hom (hP : P ≤ Q) (hS : S ≤ T)
    {X Y : D} {f : X ⟶ Y} {R : RightResolution P S X} {R' : RightResolution P S Y}
    (m : Map f R R') :
    (map hP hS m).hom = m.hom := sorry

/-- Transporting the identity map gives the identity map of the weakened right resolution. -/
@[simp]
theorem map_id (hP : P ≤ Q) (hS : S ≤ T)
    {X : D} (R : RightResolution P S X) :
    map hP hS (Map.id R) = Map.id (R.mapOfLE hP hS) := sorry

/-- Transporting a composite of right-resolution maps agrees with composing their transports. -/
@[simp]
theorem map_comp (hP : P ≤ Q) (hS : S ≤ T)
    {X Y Z : D} {f : X ⟶ Y} {g : Y ⟶ Z}
    {R : RightResolution P S X} {R' : RightResolution P S Y}
    {R'' : RightResolution P S Z} (m : Map f R R') (n : Map g R' R'') :
    map hP hS (Map.comp m n) = Map.comp (map hP hS m) (map hP hS n) := sorry

/-- Transporting a reindexed right-resolution map agrees with reindexing its transport. -/
@[simp]
theorem map_reindex (hP : P ≤ Q) (hS : S ≤ T)
    {X Y : D} {f f' : X ⟶ Y} {R : RightResolution P S X}
    {R' : RightResolution P S Y} (e : f = f') (m : Map f R R') :
    map hP hS (Map.reindex e m) = Map.reindex e (map hP hS m) := sorry

end CategoryTheory.ObjectProperty.RightResolution.mapOfLE
