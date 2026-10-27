/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Computation
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Functoriality
import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of bounded exact derived functors

Morphisms of bundled exact functors induce natural transformations between
their bounded-below, bounded-above, and bounded derived restrictions.  Thus
each restriction is itself functorial in the exact functor.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty
open DerivedCategory.TStructure

noncomputable section

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory.ExactFunctor.Derived

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]

namespace Plus

/-- The natural transformation between bounded-below restrictions induced
by a morphism of exact functors. -/
@[stacks 015F "exact natural transformations on bounded-below derived categories"]
noncomputable def map {F G : A ⥤ₑ B} (α : F ⟶ G) :
    functor F ⟶ functor G :=
  ObjectProperty.FullSubcategory.restrict.natTrans
    (mapsTo F) (mapsTo G) (ExactFunctor.MapDerivedCategory.map α)

/-- Component computation for the bounded-below derived action on an exact
natural transformation. -/
@[simp, stacks 015F "bounded-below exact derived transformation component"]
theorem map_app_hom {F G : A ⥤ₑ B} (α : F ⟶ G)
    (X : DerivedCategory.Plus A) :
    ((map α).app X).hom =
      (ExactFunctor.MapDerivedCategory.map α).app X.obj := rfl

/-- The bounded-below derived action preserves identity transformations. -/
@[simp]
theorem map_id (F : A ⥤ₑ B) : map (𝟙 F) = 𝟙 (functor F) := by
  apply NatTrans.ext
  funext X
  apply ObjectProperty.hom_ext
  change (ExactFunctor.MapDerivedCategory.map (𝟙 F)).app X.obj = 𝟙 _
  simp only [ExactFunctor.MapDerivedCategory.map, ObjectProperty.FullSubcategory.id_hom,
    NatTrans.mapHomologicalComplex_id, Functor.whiskerRight_id',
    Localization.liftNatTrans_id, NatTrans.id_app]

/-- The bounded-below derived action preserves vertical composition. -/
@[simp]
theorem map_comp {F G H : A ⥤ₑ B} (α : F ⟶ G) (β : G ⟶ H) :
    map (α ≫ β) = map α ≫ map β := by
  apply NatTrans.ext
  funext X
  apply ObjectProperty.hom_ext
  change (ExactFunctor.MapDerivedCategory.map (α ≫ β)).app X.obj =
    (ExactFunctor.MapDerivedCategory.map α).app X.obj ≫
      (ExactFunctor.MapDerivedCategory.map β).app X.obj
  simp only [ExactFunctor.MapDerivedCategory.map, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.mapHomologicalComplex_comp, Functor.whiskerRight_comp]
  exact (congr_app (Localization.comp_liftNatTrans
    (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A)
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) _ _ _
    F.mapDerivedCategory G.mapDerivedCategory H.mapDerivedCategory _ _) X.obj).symm

variable (A B) in
/-- Functorial passage from exact functors to their bounded-below derived
restrictions. -/
@[stacks 015F "functorial exact action on bounded-below derived categories"]
noncomputable def mapFunctor :
    (A ⥤ₑ B) ⥤ (DerivedCategory.Plus A ⥤ DerivedCategory.Plus B) :=
  ObjectProperty.FullSubcategory.restrict.functor
    (ExactFunctor.MapDerivedCategory.functor A B) (fun F ↦ mapsTo F)

/-- An isomorphism of exact functors induces an isomorphism of their
bounded-below derived restrictions. -/
@[stacks 015F "exact natural isomorphisms on bounded-below derived categories"]
noncomputable def mapIso {F G : A ⥤ₑ B} (e : F ≅ G) :
    functor F ≅ functor G :=
  ObjectProperty.FullSubcategory.restrict.natIso
    (mapsTo F) (mapsTo G) (ExactFunctor.MapDerivedCategory.mapIso e)

end Plus

namespace Minus

/-- The natural transformation between bounded-above restrictions induced
by a morphism of exact functors. -/
@[stacks 015F "exact natural transformations on bounded-above derived categories"]
noncomputable def map {F G : A ⥤ₑ B} (α : F ⟶ G) :
    functor F ⟶ functor G :=
  ObjectProperty.FullSubcategory.restrict.natTrans
    (mapsTo F) (mapsTo G) (ExactFunctor.MapDerivedCategory.map α)

/-- Component computation for the bounded-above derived action on an exact
natural transformation. -/
@[simp, stacks 015F "bounded-above exact derived transformation component"]
theorem map_app_hom {F G : A ⥤ₑ B} (α : F ⟶ G)
    (X : DerivedCategory.Minus A) :
    ((map α).app X).hom =
      (ExactFunctor.MapDerivedCategory.map α).app X.obj := rfl

/-- The bounded-above derived action preserves identity transformations. -/
@[simp]
theorem map_id (F : A ⥤ₑ B) : map (𝟙 F) = 𝟙 (functor F) := by
  apply NatTrans.ext
  funext X
  apply ObjectProperty.hom_ext
  change (ExactFunctor.MapDerivedCategory.map (𝟙 F)).app X.obj = 𝟙 _
  simp only [ExactFunctor.MapDerivedCategory.map, ObjectProperty.FullSubcategory.id_hom,
    NatTrans.mapHomologicalComplex_id, Functor.whiskerRight_id',
    Localization.liftNatTrans_id, NatTrans.id_app]

/-- The bounded-above derived action preserves vertical composition. -/
@[simp]
theorem map_comp {F G H : A ⥤ₑ B} (α : F ⟶ G) (β : G ⟶ H) :
    map (α ≫ β) = map α ≫ map β := by
  apply NatTrans.ext
  funext X
  apply ObjectProperty.hom_ext
  change (ExactFunctor.MapDerivedCategory.map (α ≫ β)).app X.obj =
    (ExactFunctor.MapDerivedCategory.map α).app X.obj ≫
      (ExactFunctor.MapDerivedCategory.map β).app X.obj
  simp only [ExactFunctor.MapDerivedCategory.map, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.mapHomologicalComplex_comp, Functor.whiskerRight_comp]
  exact (congr_app (Localization.comp_liftNatTrans
    (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A)
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) _ _ _
    F.mapDerivedCategory G.mapDerivedCategory H.mapDerivedCategory _ _) X.obj).symm

variable (A B) in
/-- Functorial passage from exact functors to their bounded-above derived
restrictions. -/
@[stacks 015F "functorial exact action on bounded-above derived categories"]
noncomputable def mapFunctor :
    (A ⥤ₑ B) ⥤ (DerivedCategory.Minus A ⥤ DerivedCategory.Minus B) :=
  ObjectProperty.FullSubcategory.restrict.functor
    (ExactFunctor.MapDerivedCategory.functor A B) (fun F ↦ mapsTo F)

/-- An isomorphism of exact functors induces an isomorphism of their
bounded-above derived restrictions. -/
@[stacks 015F "exact natural isomorphisms on bounded-above derived categories"]
noncomputable def mapIso {F G : A ⥤ₑ B} (e : F ≅ G) :
    functor F ≅ functor G :=
  ObjectProperty.FullSubcategory.restrict.natIso
    (mapsTo F) (mapsTo G) (ExactFunctor.MapDerivedCategory.mapIso e)

end Minus

namespace Bounded

/-- The natural transformation between bounded restrictions induced by a
morphism of exact functors. -/
@[stacks 015F "exact natural transformations on bounded derived categories"]
noncomputable def map {F G : A ⥤ₑ B} (α : F ⟶ G) :
    functor F ⟶ functor G :=
  ObjectProperty.FullSubcategory.restrict.natTrans
    (mapsTo F) (mapsTo G) (ExactFunctor.MapDerivedCategory.map α)

/-- Component computation for the bounded derived action on an exact
natural transformation. -/
@[simp, stacks 015F "bounded exact derived transformation component"]
theorem map_app_hom {F G : A ⥤ₑ B} (α : F ⟶ G)
    (X : DerivedCategory.Bounded A) :
    ((map α).app X).hom =
      (ExactFunctor.MapDerivedCategory.map α).app X.obj := rfl

/-- The bounded derived action preserves identity transformations. -/
@[simp]
theorem map_id (F : A ⥤ₑ B) : map (𝟙 F) = 𝟙 (functor F) := by
  apply NatTrans.ext
  funext X
  apply ObjectProperty.hom_ext
  change (ExactFunctor.MapDerivedCategory.map (𝟙 F)).app X.obj = 𝟙 _
  simp only [ExactFunctor.MapDerivedCategory.map, ObjectProperty.FullSubcategory.id_hom,
    NatTrans.mapHomologicalComplex_id, Functor.whiskerRight_id',
    Localization.liftNatTrans_id, NatTrans.id_app]

/-- The bounded derived action preserves vertical composition. -/
@[simp]
theorem map_comp {F G H : A ⥤ₑ B} (α : F ⟶ G) (β : G ⟶ H) :
    map (α ≫ β) = map α ≫ map β := by
  apply NatTrans.ext
  funext X
  apply ObjectProperty.hom_ext
  change (ExactFunctor.MapDerivedCategory.map (α ≫ β)).app X.obj =
    (ExactFunctor.MapDerivedCategory.map α).app X.obj ≫
      (ExactFunctor.MapDerivedCategory.map β).app X.obj
  simp only [ExactFunctor.MapDerivedCategory.map, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.mapHomologicalComplex_comp, Functor.whiskerRight_comp]
  exact (congr_app (Localization.comp_liftNatTrans
    (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A)
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) _ _ _
    F.mapDerivedCategory G.mapDerivedCategory H.mapDerivedCategory _ _) X.obj).symm

variable (A B) in
/-- Functorial passage from exact functors to their bounded derived
restrictions. -/
@[stacks 015F "functorial exact action on bounded derived categories"]
noncomputable def mapFunctor :
    (A ⥤ₑ B) ⥤ (DerivedCategory.Bounded A ⥤ DerivedCategory.Bounded B) :=
  ObjectProperty.FullSubcategory.restrict.functor
    (ExactFunctor.MapDerivedCategory.functor A B) (fun F ↦ mapsTo F)

/-- An isomorphism of exact functors induces an isomorphism of their bounded
derived restrictions. -/
@[stacks 015F "exact natural isomorphisms on bounded derived categories"]
noncomputable def mapIso {F G : A ⥤ₑ B} (e : F ≅ G) :
    functor F ≅ functor G :=
  ObjectProperty.FullSubcategory.restrict.natIso
    (mapsTo F) (mapsTo G) (ExactFunctor.MapDerivedCategory.mapIso e)

end Bounded

end CategoryTheory.ExactFunctor.Derived
