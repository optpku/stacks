module

public import stacks_project.Chap64.Lemma_64_7_2_Projective
public import stacks_project.Chap64.Lemma_64_7_2_Minus
public import ReasLib.CategoryTheory.Filtration.Derived.BoundedLocalization
public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Functor
public import ReasLib.CategoryTheory.Preadditive.RightExact
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Filtered left-derived functors of right-exact functors

This module supplies the object-level map of a right-exact (or merely additive) functor on
finite filtered-projective objects, the induced bounded-above homotopy functor, and the
filtered left-derived functor `LG : DF⁻(A) ⥤ DF⁻(B)` obtained by transporting along the
filtered-projective model of Lemma 64.7.2.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.FilteredObject.Finite.FilteredProjective

variable {A : Type u₁} {B : Type u₂}
  [_root_.CategoryTheory.Category.{v₁} A]
  [_root_.CategoryTheory.Category.{v₂} B]
  [Abelian A] [Abelian B]

/-- The finite filtered object obtained by applying an additive functor to a finite
filtered-projective object. Stages are the images of the original stage inclusions; this is
the Subobject.mk construction of Filtration.Map, adapted to functors that need not preserve
monomorphisms. -/
noncomputable def map (G : A ⥤ B) [G.Additive] (P : category A) : FilteredObject B where
  obj := G.obj P.obj.obj.obj
  filtration :=
    { toFun := fun i ↦ imageSubobject (G.map (P.obj.obj.filtration i).arrow)
      monotone' := sorry }

/-- The underlying object of `map G P` is the image of the underlying object of `P`. -/
@[simp]
theorem map_obj (G : A ⥤ B) [G.Additive] (P : category A) :
    (map G P).obj = G.obj P.obj.obj.obj := sorry

/-- The `p`-th stage of `map G P` is the image of the original `p`-th stage inclusion. -/
@[simp]
theorem map_stage (G : A ⥤ B) [G.Additive] (P : category A) (p : ℤ) :
    (map G P).filtration.stage p =
      imageSubobject (G.map (P.obj.obj.filtration.stage p).arrow) := sorry

/-- Applying an additive functor to a finite filtered-projective object preserves finiteness of
the filtration. -/
theorem map_isFinite (G : A ⥤ B) [G.Additive] (P : category A) : (map G P).IsFinite := sorry

/-- The filtration-preserving morphism induced by applying an additive functor to a morphism of
finite filtered-projective objects. -/
noncomputable def homMap (G : A ⥤ B) [G.Additive] {P Q : category A} (f : P ⟶ Q) :
    map G P ⟶ map G Q where
  hom := G.map f.hom.hom.hom
  preserves := sorry

/-- `homMap` sends identity morphisms to identities. -/
theorem homMap_id (G : A ⥤ B) [G.Additive] (P : category A) :
    homMap G (𝟙 P) = 𝟙 (map G P) := sorry

/-- `homMap` preserves composition. -/
theorem homMap_comp (G : A ⥤ B) [G.Additive] {P Q R : category A} (f : P ⟶ Q) (g : Q ⟶ R) :
    homMap G (f ≫ g) = homMap G f ≫ homMap G g := sorry

/-- The functor on finite filtered-projective objects induced by an additive functor, landing in
finite filtered objects. This is the object-level bottom arrow of the source square for `LG`. -/
noncomputable def mapFunctor (G : A ⥤ B) [G.Additive] :
    category A ⥤ FilteredObject.Finite.category B :=
  ObjectProperty.lift (FilteredObject.IsFinite : ObjectProperty (FilteredObject B))
    { obj := map G
      map := homMap G
      map_id := homMap_id G
      map_comp := homMap_comp G }
    fun P ↦ map_isFinite G P

/-- Objectwise computation for `mapFunctor`. -/
@[simp]
theorem mapFunctor_obj (G : A ⥤ B) [G.Additive] (P : category A) :
    ((mapFunctor G).obj P).obj = map G P := sorry

/-- Morphismwise computation for `mapFunctor`. -/
@[simp]
theorem mapFunctor_map (G : A ⥤ B) [G.Additive] {P Q : category A} (f : P ⟶ Q) :
    ((mapFunctor G).map f).hom = homMap G f := sorry

/-- The functor on finite filtered-projective objects induced by an additive functor is
additive. -/
instance mapFunctor_additive (G : A ⥤ B) [G.Additive] : (mapFunctor G).Additive := sorry

end CategoryTheory.FilteredObject.Finite.FilteredProjective

namespace CategoryTheory.FilteredObject.FiniteDerived.Minus.RightExact

variable {A : Type u₁} {B : Type u₂}
  [_root_.CategoryTheory.Category.{v₁} A]
  [_root_.CategoryTheory.Category.{v₂} B]
  [Abelian A] [Abelian B]

/-- The bounded-above homotopy functor induced by applying a right-exact functor to finite
filtered-projective objects. This is the bottom arrow `K⁻(P) --G--> K⁻(Filᶠ(B))` of the source
square. -/
noncomputable def homotopy (G : A ⥤ᵣ B) :
    HomotopyCategory.Minus (Finite.FilteredProjective.category A) ⥤
      HomotopyCategory.Minus (FilteredObject.Finite.category B) :=
  (Finite.FilteredProjective.mapFunctor G.obj).mapHomotopyCategoryMinus

/-- Objectwise computation for the bounded-above homotopy functor induced by `G`. -/
@[simp]
theorem homotopy_obj_obj (G : A ⥤ᵣ B)
    (K : HomotopyCategory.Minus (Finite.FilteredProjective.category A)) :
    ((homotopy G).obj K).obj =
      ((Finite.FilteredProjective.mapFunctor G.obj).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj K.obj := sorry

variable [HasDerivedCategory (GradedObject ℤ A)]
  [HasDerivedCategory (GradedObject ℤ B)]

/-- The filtered left-derived functor of a right-exact functor, obtained by transporting the
homotopy-level map along the filtered-projective equivalence of Lemma 64.7.2. -/
noncomputable def functor (G : A ⥤ᵣ B) [EnoughProjectives A]
    (hA : AssociatedGraded.Inverts A) (hB : AssociatedGraded.Inverts B) :
    Minus.Category A hA ⥤ Minus.Category B hB :=
  (Minus.FilteredProjective.equivalenceOfEnoughProjectives A hA).inverse ⋙
    homotopy G ⋙ Minus.Quotient.functor B hB

/-- Unfolding of the filtered left-derived functor of a right-exact functor. -/
theorem functor_eq (G : A ⥤ᵣ B) [EnoughProjectives A]
    (hA : AssociatedGraded.Inverts A) (hB : AssociatedGraded.Inverts B) :
    functor G hA hB =
      (Minus.FilteredProjective.equivalenceOfEnoughProjectives A hA).inverse ⋙
        homotopy G ⋙ Minus.Quotient.functor B hB := sorry

/-- The source square identifying `LG` after the filtered-projective model: the composite
through `DF⁻(A)` agrees with mapping by `G` and then passing to `DF⁻(B)`. -/
noncomputable def diagramIso (G : A ⥤ᵣ B) [EnoughProjectives A]
    (hA : AssociatedGraded.Inverts A) (hB : AssociatedGraded.Inverts B) :
    Minus.FilteredProjective.functor A hA ⋙ functor G hA hB ≅
      homotopy G ⋙ Minus.Quotient.functor B hB :=
  (Minus.FilteredProjective.equivalenceOfEnoughProjectives A hA).funInvIdAssoc
    (homotopy G ⋙ Minus.Quotient.functor B hB)

/-- Component form of `diagramIso` at a bounded-above filtered-projective homotopy object. -/
theorem diagramIso_hom_app (G : A ⥤ᵣ B) [EnoughProjectives A]
    (hA : AssociatedGraded.Inverts A) (hB : AssociatedGraded.Inverts B)
    (K : HomotopyCategory.Minus (Finite.FilteredProjective.category A)) :
    (diagramIso G hA hB).hom.app K =
      (homotopy G ⋙ Minus.Quotient.functor B hB).map
        ((Minus.FilteredProjective.equivalenceOfEnoughProjectives A hA).unitInv.app K) :=
  sorry

end CategoryTheory.FilteredObject.FiniteDerived.Minus.RightExact
