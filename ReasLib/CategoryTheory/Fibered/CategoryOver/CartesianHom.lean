module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.Fiber
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cartesian based functors as fixed-owner morphisms

For fixed fibred categories `X` and `Y`, the hom-category `X ⟶ Y` and the category of
cartesian based functors `CartesianBasedFunctor X.p Y.p` have the same mathematical data. This
file gives the explicit equivalence between the universe-polymorphic presentation and the
fixed-owner presentation used by `FiberedCategoryOver`.

The conversion functors retain the supplied based functors and vertical natural transformations;
they do not choose representatives or inverse data.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe u v w vS

namespace CategoryTheory

namespace FiberedCategoryOver.CartesianHom

variable {C : Type u} [Category.{v} C]
variable (X Y : FiberedCategoryOver.{u, v, w, vS} C)

namespace toHom

/-- The fixed-owner morphism with the same based functor and cartesian-preservation witness as
the supplied cartesian based functor. -/
def obj (F : CartesianBasedFunctor X.p Y.p) : X ⟶ Y :=
  FiberedCategoryOver.ofBasedFunctor
    F.toBasedFunctor F.preservesStronglyCartesian

/-- The fixed-owner `2`-morphism with the same vertical based natural transformation as the
supplied morphism of cartesian based functors. -/
def map {F G : CartesianBasedFunctor X.p Y.p} (η : F ⟶ G) :
    obj X Y F ⟶ obj X Y G :=
  FiberedCategoryOver.ofBasedNatTrans η.hom

/-- The fixed-owner conversion preserves identity morphisms. -/
theorem map_id (F : CartesianBasedFunctor X.p Y.p) :
    map X Y (𝟙 F) = 𝟙 (obj X Y F) := sorry

/-- The fixed-owner conversion preserves composition. -/
theorem map_comp {F G H : CartesianBasedFunctor X.p Y.p}
    (η : F ⟶ G) (θ : G ⟶ H) :
    map X Y (η ≫ θ) = map X Y η ≫ map X Y θ := sorry

end toHom

/-- Regard a cartesian based functor between the projections of two fixed fibred categories as
a morphism in their hom-category. -/
def toHom : CartesianBasedFunctor X.p Y.p ⥤ (X ⟶ Y) where
  obj := toHom.obj X Y
  map := toHom.map X Y
  map_id := toHom.map_id X Y
  map_comp := toHom.map_comp X Y

namespace fromHom

/-- The cartesian based functor underlying a morphism of fixed fibred categories. -/
def obj (F : X ⟶ Y) : CartesianBasedFunctor X.p Y.p :=
  FiberedCategoryOver.toCartesianBasedFunctor F

/-- The morphism of cartesian based functors with the same vertical based natural
transformation as the supplied fixed-owner `2`-morphism. -/
def map {F G : X ⟶ Y} (η : F ⟶ G) : obj X Y F ⟶ obj X Y G :=
  CartesianBasedFunctor.homMk η.hom

/-- Forgetting to cartesian based functors preserves identity `2`-morphisms. -/
theorem map_id (F : X ⟶ Y) :
    map X Y (𝟙 F) = 𝟙 (obj X Y F) := sorry

/-- Forgetting to cartesian based functors preserves composition of `2`-morphisms. -/
theorem map_comp {F G H : X ⟶ Y} (η : F ⟶ G) (θ : G ⟶ H) :
    map X Y (η ≫ θ) = map X Y η ≫ map X Y θ := sorry

end fromHom

/-- Forget a morphism between fixed fibred categories to its cartesian based functor. -/
def fromHom : (X ⟶ Y) ⥤ CartesianBasedFunctor X.p Y.p where
  obj := fromHom.obj X Y
  map := fromHom.map X Y
  map_id := fromHom.map_id X Y
  map_comp := fromHom.map_comp X Y

namespace toHom

/-- The fixed-owner conversion retains the underlying based functor. -/
@[simp]
theorem obj_toBasedFunctor (F : CartesianBasedFunctor X.p Y.p) :
    FiberedCategoryOver.toBasedFunctor ((toHom X Y).obj F) = F.toBasedFunctor := sorry

/-- The fixed-owner conversion retains the functor between total categories. -/
@[simp]
theorem obj_toFunctor (F : CartesianBasedFunctor X.p Y.p) :
    FiberedCategoryOver.toFunctor ((toHom X Y).obj F) = F.toFunctor := sorry

/-- The fixed-owner conversion retains the strict projection equation. -/
@[simp]
theorem obj_comm (F : CartesianBasedFunctor X.p Y.p) :
    FiberedCategoryOver.comm ((toHom X Y).obj F) = F.toBasedFunctor.w := sorry

/-- The fixed-owner conversion retains the underlying vertical based natural transformation. -/
@[simp]
theorem map_toBasedNatTrans
    {F G : CartesianBasedFunctor X.p Y.p} (η : F ⟶ G) :
    FiberedCategoryOver.toBasedNatTrans ((toHom X Y).map η) = η.hom := sorry

/-- Converting a fixed-owner morphism to a cartesian based functor and back recovers it. -/
@[simp]
theorem obj_fromHom (F : X ⟶ Y) :
    (toHom X Y).obj ((fromHom X Y).obj F) = F := sorry

end toHom

namespace fromHom

/-- Forgetting a fixed-owner morphism retains its underlying based functor. -/
@[simp]
theorem obj_toBasedFunctor (F : X ⟶ Y) :
    ((fromHom X Y).obj F).toBasedFunctor =
      FiberedCategoryOver.toBasedFunctor F := sorry

/-- Forgetting a fixed-owner `2`-morphism retains its underlying vertical based natural
transformation. -/
@[simp]
theorem map_toBasedNatTrans {F G : X ⟶ Y} (η : F ⟶ G) :
    CartesianBasedFunctor.toBasedNatTrans ((fromHom X Y).map η) =
      FiberedCategoryOver.toBasedNatTrans η := sorry

/-- Converting a cartesian based functor to a fixed-owner morphism and back recovers it. -/
@[simp]
theorem obj_toHom (F : CartesianBasedFunctor X.p Y.p) :
    (fromHom X Y).obj ((toHom X Y).obj F) = F := sorry

end fromHom

namespace unitIso

/-- Naturality of the identity comparison from a cartesian based functor to its round trip
through the fixed-owner hom-category. -/
theorem naturality {F G : CartesianBasedFunctor X.p Y.p} (η : F ⟶ G) :
    η ≫ (Iso.refl G).hom =
      (Iso.refl F).hom ≫ ((toHom X Y) ⋙ (fromHom X Y)).map η := sorry

end unitIso

/-- The identity comparison from cartesian based functors to their fixed-owner round trip. -/
def unitIso :
    𝟭 (CartesianBasedFunctor X.p Y.p) ≅ toHom X Y ⋙ fromHom X Y :=
  NatIso.ofComponents (fun F ↦ Iso.refl F)
    (fun η ↦ unitIso.naturality X Y η)

namespace counitIso

/-- Naturality of the identity comparison from the fixed-owner round trip to a morphism of
fibred categories. -/
theorem naturality {F G : X ⟶ Y} (η : F ⟶ G) :
    ((fromHom X Y) ⋙ (toHom X Y)).map η ≫ (Iso.refl G).hom =
      (Iso.refl F).hom ≫ η := sorry

end counitIso

/-- The identity comparison from the fixed-owner round trip to the original hom-category. -/
def counitIso : fromHom X Y ⋙ toHom X Y ≅ 𝟭 (X ⟶ Y) :=
  NatIso.ofComponents (fun F ↦ Iso.refl F)
    (fun η ↦ counitIso.naturality X Y η)

/-- The triangle identity for the explicit fixed-owner comparison. -/
theorem functor_unitIso_comp (F : CartesianBasedFunctor X.p Y.p) :
    (toHom X Y).map ((unitIso X Y).hom.app F) ≫
        (counitIso X Y).hom.app ((toHom X Y).obj F) =
      𝟙 ((toHom X Y).obj F) := sorry

/-- Cartesian based functors between fixed projections are canonically equivalent to the
hom-category of the corresponding fibred-category owners. -/
def equivalence : CartesianBasedFunctor X.p Y.p ≌ (X ⟶ Y) where
  functor := toHom X Y
  inverse := fromHom X Y
  unitIso := unitIso X Y
  counitIso := counitIso X Y
  functor_unitIso_comp := functor_unitIso_comp X Y

end FiberedCategoryOver.CartesianHom

end CategoryTheory

/- Axiom audit: both functors preserve the supplied based functor and vertical transformation
data. The fixed-owner hom type inherits `sorryAx` from upstream category-law proofs; the only
proof debt introduced in this file is in functor laws, naturality, computation statements, and
the triangle identity. -/
