module

public import ReasLib.CategoryTheory.ObjectProperty.Localization.Resolution.Left.Map
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Resolution.Left.Monotonicity
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Monotonicity of Maps of Property-Indexed Left Resolutions

Weakening the object and comparison properties of left resolutions also transports maps over
arbitrary target morphisms.  The transport leaves the ambient morphism unchanged and is compatible
with the identity, composition, and reindexing operations.
-/

@[expose] public section

universe v u

namespace CategoryTheory.ObjectProperty.LeftResolution.mapOfLE

variable {D : Type u} [Category.{v} D]
  {P Q : ObjectProperty D} {S T : MorphismProperty D}

/-- The image of a left-resolution map under weaker model and comparison properties satisfies
the required comparison square. -/
theorem map_naturality (hP : P ≤ Q) (hS : S ≤ T)
    {X Y : D} {f : X ⟶ Y} {R : LeftResolution P S X} {R' : LeftResolution P S Y}
    (m : Map f R R') :
    Q.ι.map ((P.ιOfLE hP).map m.modelHom) ≫
        (R'.mapOfLE hP hS).comparison =
      (R.mapOfLE hP hS).comparison ≫ f := sorry

/-- Transport a map of left resolutions after weakening the model and comparison properties. -/
@[stacks 0GSL "monotonicity of maps of left resolutions"]
def map (hP : P ≤ Q) (hS : S ≤ T)
    {X Y : D} {f : X ⟶ Y} {R : LeftResolution P S X} {R' : LeftResolution P S Y}
    (m : Map f R R') :
    Map f (R.mapOfLE hP hS) (R'.mapOfLE hP hS) :=
  Map.mk ((P.ιOfLE hP).map m.modelHom) (map_naturality hP hS m)

/-- Transporting a left-resolution map applies `ObjectProperty.ιOfLE` to its bundled model
morphism. -/
@[simp]
theorem map_modelHom (hP : P ≤ Q) (hS : S ≤ T)
    {X Y : D} {f : X ⟶ Y} {R : LeftResolution P S X} {R' : LeftResolution P S Y}
    (m : Map f R R') :
    (map hP hS m).modelHom = (P.ιOfLE hP).map m.modelHom := sorry

/-- Transporting a left-resolution map retains its ambient morphism. -/
@[simp]
theorem map_hom (hP : P ≤ Q) (hS : S ≤ T)
    {X Y : D} {f : X ⟶ Y} {R : LeftResolution P S X} {R' : LeftResolution P S Y}
    (m : Map f R R') :
    (map hP hS m).hom = m.hom := sorry

/-- Transporting the identity map gives the identity map of the weakened left resolution. -/
@[simp]
theorem map_id (hP : P ≤ Q) (hS : S ≤ T)
    {X : D} (R : LeftResolution P S X) :
    map hP hS (Map.id R) = Map.id (R.mapOfLE hP hS) := sorry

/-- Transporting a composite of left-resolution maps agrees with composing their transports. -/
@[simp]
theorem map_comp (hP : P ≤ Q) (hS : S ≤ T)
    {X Y Z : D} {f : X ⟶ Y} {g : Y ⟶ Z}
    {R : LeftResolution P S X} {R' : LeftResolution P S Y}
    {R'' : LeftResolution P S Z} (m : Map f R R') (n : Map g R' R'') :
    map hP hS (Map.comp m n) = Map.comp (map hP hS m) (map hP hS n) := sorry

/-- Transporting a reindexed left-resolution map agrees with reindexing its transport. -/
@[simp]
theorem map_reindex (hP : P ≤ Q) (hS : S ≤ T)
    {X Y : D} {f f' : X ⟶ Y} {R : LeftResolution P S X}
    {R' : LeftResolution P S Y} (e : f = f') (m : Map f R R') :
    map hP hS (Map.reindex e m) = Map.reindex e (map hP hS m) := sorry

end CategoryTheory.ObjectProperty.LeftResolution.mapOfLE
