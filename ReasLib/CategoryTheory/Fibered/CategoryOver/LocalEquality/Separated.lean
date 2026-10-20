module

public import Mathlib.CategoryTheory.Sites.Grothendieck
public import ReasLib.CategoryTheory.Fibered.CategoryOver.LocalEquality
public import ReasLib.CategoryTheory.Fibered.HomPresheaf
public import ReasLib.CategoryTheory.Sites.TypeSheafification

/-!
# Separated Hom presheaves of local-equality quotients

The local-equality quotient makes its fiberwise Hom presheaves separated.  This
site-local leaf exposes both the canonical Hom-presheaf form and the arbitrary
base-arrow form used by plus constructions.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open scoped CategoryTheory.Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.LocalEquality.QuotientTotal

/-- Every canonical fiber Hom presheaf of the local-equality quotient is separated for the
induced topology on the corresponding slice category. -/
theorem HomPresheaf.isSeparated
    (J : GrothendieckTopology C) (X : FiberedCategoryOver.{u, v, w, vS} C) {U : C}
    (x y : (projection J X).Fiber U) :
    Presieve.IsSeparated (J.over U)
      ((Functor.fiberPseudofunctor (projection J X)).presheafHom x y) := sorry

/-- The local Hom presheaf over an arbitrary base arrow in the local-equality quotient is
separated. -/
theorem LocalHom.Presheaf.isSeparated
    (J : GrothendieckTopology C) (X : FiberedCategoryOver.{u, v, w, vS} C)
    {U V : C} (x : (projection J X).Fiber U) (f : U ⟶ V)
    (y : (projection J X).Fiber V) :
    Presieve.IsSeparated (J.over U)
      (Functor.LocalHom.Presheaf.apply (projection J X) x f y) := sorry

/-- The plus construction of the universe-raised local Hom presheaf of a local-equality quotient
is a sheaf on the slice site, by the generic separated-presheaf plus theorem. -/
theorem LocalHom.Presheaf.ULift.plusIsSheaf
    (J : GrothendieckTopology C) (X : FiberedCategoryOver.{u, v, w, vS} C)
    {U V : C} (x : (projection J X).Fiber U) (f : U ⟶ V)
    (y : (projection J X).Fiber V) :
    Presheaf.IsSheaf (J.over U)
      ((J.over U).plusObj (Functor.LocalHom.Presheaf.ULift.apply (projection J X) x f y)) := sorry

/-- The canonical map from a universe-raised local Hom presheaf to its plus construction is a
`W`-morphism on the corresponding slice site. -/
theorem LocalHom.Presheaf.ULift.toPlus_mem_W
    (J : GrothendieckTopology C) (X : FiberedCategoryOver.{u, v, w, vS} C)
    {U V : C} (x : (projection J X).Fiber U) (f : U ⟶ V)
    (y : (projection J X).Fiber V) :
    (J.over U).W
      ((J.over U).toPlus (Functor.LocalHom.Presheaf.ULift.apply (projection J X) x f y)) := sorry

end FiberedCategoryOver.LocalEquality.QuotientTotal

end CategoryTheory
