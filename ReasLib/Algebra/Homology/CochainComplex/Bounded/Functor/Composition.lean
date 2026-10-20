module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Functor.Basic
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Composition

@[expose] public section

/-!
# Composition of functors on bounded cochain complexes

The comparison for bounded-above and bounded complexes is obtained from the neutral
composition API for restriction to full subcategories.  The bounded-below comparison is
included to give the three boundedness variants a uniform public interface.
-/

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.Cochain

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D]
  {E : Type*} [Category E] [Preadditive E]
  {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
  [F.Additive] [G.Additive] [H.Additive]

namespace Plus

/-- Composition comparison for the bounded-below cochain functors supplied by Mathlib. -/
def compIso (e : F ⋙ G ≅ H) :
    F.mapCochainComplexPlus ⋙ G.mapCochainComplexPlus ≅
      H.mapCochainComplexPlus :=
  ((CochainComplex.Plus.fullyFaithfulι E).whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (CochainComplex.Plus.ι C)
      (Functor.mapHomologicalComplexCompIso e (up ℤ)))

/-- The underlying forward component of the bounded-below composition comparison is the
ambient termwise comparison. -/
@[simp]
theorem compIso_hom_app_hom (e : F ⋙ G ≅ H) (K : CochainComplex.Plus C) :
    ((compIso e).hom.app K).hom =
      (Functor.mapHomologicalComplexCompIso e (up ℤ)).hom.app K.obj := sorry

/-- The underlying inverse component of the bounded-below composition comparison is the
ambient termwise comparison. -/
@[simp]
theorem compIso_inv_app_hom (e : F ⋙ G ≅ H) (K : CochainComplex.Plus C) :
    ((compIso e).inv.app K).hom =
      (Functor.mapHomologicalComplexCompIso e (up ℤ)).inv.app K.obj := sorry

end Plus

namespace Minus

/-- Composition comparison for bounded-above cochain functors. -/
def compIso (e : F ⋙ G ≅ H) :
    map F ⋙ map G ≅ map H :=
  (ObjectProperty.FullSubcategory.restrict.compIso
      (F.mapHomologicalComplex (up ℤ)) (G.mapHomologicalComplex (up ℤ))
      (mapsTo F) (mapsTo G)).symm ≪≫
    ObjectProperty.FullSubcategory.restrict.natIso
      (ObjectProperty.FullSubcategory.restrict.mapsToComp
        (mapsTo F) (mapsTo G))
      (mapsTo H) (Functor.mapHomologicalComplexCompIso e (up ℤ))

/-- The underlying forward component of the bounded-above composition comparison is the
ambient termwise comparison. -/
@[simp]
theorem compIso_hom_app_hom (e : F ⋙ G ≅ H) (K : CochainComplex.Minus C) :
    ((compIso e).hom.app K).hom =
      (Functor.mapHomologicalComplexCompIso e (up ℤ)).hom.app K.obj := sorry

/-- The underlying inverse component of the bounded-above composition comparison is the
ambient termwise comparison. -/
@[simp]
theorem compIso_inv_app_hom (e : F ⋙ G ≅ H) (K : CochainComplex.Minus C) :
    ((compIso e).inv.app K).hom =
      (Functor.mapHomologicalComplexCompIso e (up ℤ)).inv.app K.obj := sorry

end Minus

namespace Bounded

/-- Composition comparison for bounded cochain functors. -/
def compIso (e : F ⋙ G ≅ H) :
    map F ⋙ map G ≅ map H :=
  (ObjectProperty.FullSubcategory.restrict.compIso
      (F.mapHomologicalComplex (up ℤ)) (G.mapHomologicalComplex (up ℤ))
      (mapsTo F) (mapsTo G)).symm ≪≫
    ObjectProperty.FullSubcategory.restrict.natIso
      (ObjectProperty.FullSubcategory.restrict.mapsToComp
        (mapsTo F) (mapsTo G))
      (mapsTo H) (Functor.mapHomologicalComplexCompIso e (up ℤ))

/-- The underlying forward component of the bounded composition comparison is the ambient
termwise comparison. -/
@[simp]
theorem compIso_hom_app_hom (e : F ⋙ G ≅ H) (K : CochainComplex.Bounded C) :
    ((compIso e).hom.app K).hom =
      (Functor.mapHomologicalComplexCompIso e (up ℤ)).hom.app K.obj := sorry

/-- The underlying inverse component of the bounded composition comparison is the ambient
termwise comparison. -/
@[simp]
theorem compIso_inv_app_hom (e : F ⋙ G ≅ H) (K : CochainComplex.Bounded C) :
    ((compIso e).inv.app K).hom =
      (Functor.mapHomologicalComplexCompIso e (up ℤ)).inv.app K.obj := sorry

end Bounded

end CategoryTheory.Functor.Cochain
