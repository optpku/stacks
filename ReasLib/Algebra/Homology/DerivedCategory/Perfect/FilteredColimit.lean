module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Composition
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.HomDiagram
public import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Perfect complexes over filtered colimits

This leaf owns the explicit stage and Hom-diagram data used for filtered-colimit descent of
perfect derived modules. The maps and comparison isomorphisms are concrete; the descent and
filtered-colimit assertions are proposition-valued statements.

@stack 0BC7
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.DerivedCategory.Perfect.FilteredColimit

variable {I : Type v} [Preorder I] [IsFiltered I]
variable (F : I ⥤ CommRingCat.{u}) [HasColimit F]

/-- The ring underlying the categorical filtered colimit of `. -/
@[stacks 0BC7 "filtered colimit ring"]
abbrev ringColimit : Type u := (colimit F : CommRingCat.{u})

/-- Derived scalar extension from a stage ring to the filtered colimit ring. -/
@[stacks 0BC7 "stage-to-colimit derived extension"]
noncomputable abbrev baseChangeToColimit (i : I) :
    DerivedCategory (ModuleCat (F.obj i)) ⥤
      DerivedCategory (ModuleCat (ringColimit F)) :=
  ModuleCat.derivedExtensionOfScalars (colimit.ι F i).hom

/-- Lemma 15.75.18 (0BC7), object descent: every perfect object over the colimit ring descends
to a perfect object over one stage. -/
@[stacks 0BC7 "perfect-object stage descent"]
theorem exists_stage_of_isPerfect
    (K : DerivedCategory (ModuleCat (ringColimit F))) (hK : K.IsPerfect) :
    ∃ (i : I) (Ki : DerivedCategory (ModuleCat (F.obj i))),
      Ki.IsPerfect ∧ IsIsomorphic K ((baseChangeToColimit F i).obj Ki) := sorry

section Hom

variable (i₀ : I)

/-- The derived extension from a fixed stage ` to a later stage `. -/
@[stacks 0BC7 "stage derived extension"]
noncomputable abbrev stageBaseChange (j : Set.Ici i₀) :
    DerivedCategory (ModuleCat (F.obj i₀)) ⥤
      DerivedCategory (ModuleCat (F.obj j.1)) :=
  ModuleCat.derivedExtensionOfScalars (F.map (homOfLE j.2)).hom

/-- The derived extension from a fixed stage to the colimit ring. -/
@[stacks 0BC7 "fixed-stage colimit extension"]
noncomputable abbrev colimitBaseChange :
    DerivedCategory (ModuleCat (F.obj i₀)) ⥤
      DerivedCategory (ModuleCat (ringColimit F)) :=
  baseChangeToColimit F i₀

/-- The derived extension from a later stage to the colimit ring. -/
@[stacks 0BC7 "later-stage colimit extension"]
noncomputable abbrev stageToColimitBaseChange (j : Set.Ici i₀) :
    DerivedCategory (ModuleCat (F.obj j.1)) ⥤
      DerivedCategory (ModuleCat (ringColimit F)) :=
  baseChangeToColimit F j.1

/-- The derived extension along a transition ` in the tail of the filtered system. -/
@[stacks 0BC7 "transition derived extension"]
noncomputable abbrev stageTransitionBaseChange {j k : Set.Ici i₀} (hjk : j ⟶ k) :
    DerivedCategory (ModuleCat (F.obj j.1)) ⥤
      DerivedCategory (ModuleCat (F.obj k.1)) :=
  ModuleCat.derivedExtensionOfScalars (F.map hjk).hom

/-- The ring-map equation identifying direct stage-to-colimit extension with two-step extension. -/
@[stacks 0BC7 "stage-to-colimit map equation"]
theorem stageToColimitBaseChange_comp_eq (j : Set.Ici i₀) :
    (colimit.ι F j.1).hom.comp (F.map (homOfLE j.2)).hom =
      (colimit.ι F i₀).hom := sorry

/-- The ring-map equation identifying a transition after the fixed stage map with the later stage
map. -/
@[stacks 0BC7 "stage transition map equation"]
theorem stageTransitionBaseChange_comp_eq {j k : Set.Ici i₀} (hjk : j ⟶ k) :
    (F.map hjk).hom.comp (F.map (homOfLE j.2)).hom =
      (F.map (homOfLE k.2)).hom := sorry

/-- The comparison isomorphism between two-step and direct extension to the colimit. -/
@[stacks 0BC7 "stage-to-colimit comparison"]
noncomputable abbrev stageToColimitBaseChangeIso (j : Set.Ici i₀) :
    stageBaseChange F i₀ j ⋙ stageToColimitBaseChange F i₀ j ≅ colimitBaseChange F i₀ :=
  ModuleCat.derivedExtensionOfScalarsCompIso
    (F.map (homOfLE j.2)).hom
    (colimit.ι F j.1).hom
    (colimit.ι F i₀).hom
    (stageToColimitBaseChange_comp_eq F i₀ j)

/-- The comparison isomorphism between extension through a later stage and direct extension to
that stage. -/
@[stacks 0BC7 "transition comparison"]
noncomputable abbrev stageTransitionBaseChangeIso {j k : Set.Ici i₀} (hjk : j ⟶ k) :
    stageBaseChange F i₀ j ⋙ stageTransitionBaseChange F i₀ hjk ≅ stageBaseChange F i₀ k :=
  ModuleCat.derivedExtensionOfScalarsCompIso
    (F.map (homOfLE j.2)).hom
    (F.map hjk).hom
    (F.map (homOfLE k.2)).hom
    (stageTransitionBaseChange_comp_eq F i₀ hjk)

/-- A Hom-set between two fixed source objects after extension to a stage. -/
@[stacks 0BC7 "stage Hom type"]
noncomputable abbrev stageHom
    (K₀ L₀ : DerivedCategory (ModuleCat (F.obj i₀))) (j : Set.Ici i₀) : Type _ :=
  (stageBaseChange F i₀ j).obj K₀ ⟶ (stageBaseChange F i₀ j).obj L₀

/-- The transition map on stage Hom-sets, transported through the comparison isomorphism. -/
@[stacks 0BC7 "stage Hom transition"]
noncomputable def stageTransitionHomMap
    (K₀ L₀ : DerivedCategory (ModuleCat (F.obj i₀)))
    {j k : Set.Ici i₀} (hjk : j ⟶ k) :
    stageHom F i₀ K₀ L₀ j → stageHom F i₀ K₀ L₀ k :=
  fun β ↦
    (stageTransitionBaseChangeIso F i₀ hjk).inv.app K₀ ≫
      (stageTransitionBaseChange F i₀ hjk).map β ≫
        (stageTransitionBaseChangeIso F i₀ hjk).hom.app L₀

/-- The image of a stage morphism in the colimit Hom-set. -/
@[stacks 0BC7 "stage-to-colimit Hom map"]
noncomputable def stageToColimitHomMap
    (K₀ L₀ : DerivedCategory (ModuleCat (F.obj i₀))) (j : Set.Ici i₀) :
    stageHom F i₀ K₀ L₀ j →
      ((colimitBaseChange F i₀).obj K₀ ⟶ (colimitBaseChange F i₀).obj L₀) :=
  fun β ↦
    (stageToColimitBaseChangeIso F i₀ j).inv.app K₀ ≫
      (stageToColimitBaseChange F i₀ j).map β ≫
        (stageToColimitBaseChangeIso F i₀ j).hom.app L₀

/-- Naturality of the stage-to-colimit Hom maps. -/
@[stacks 0BC7 "stage-to-colimit Hom naturality"]
theorem stageToColimitHomMap_natural
    (K₀ L₀ : DerivedCategory (ModuleCat (F.obj i₀)))
    {j k : Set.Ici i₀} (hjk : j ⟶ k) (β : stageHom F i₀ K₀ L₀ j) :
    stageToColimitHomMap F i₀ K₀ L₀ k (stageTransitionHomMap F i₀ K₀ L₀ hjk β) =
      stageToColimitHomMap F i₀ K₀ L₀ j β := sorry

/-- The identity transition induces the identity morphism between stage Hom types. -/
@[stacks 0BC7 "identity law for stage Hom transition"]
theorem stageTransitionHomMap_id
    (K₀ L₀ : DerivedCategory (ModuleCat (F.obj i₀))) (j : Set.Ici i₀) :
    TypeCat.ofHom (stageTransitionHomMap F i₀ K₀ L₀ (𝟙 j)) = 𝟙 _ := sorry

/-- Stage Hom transitions respect composition. -/
@[stacks 0BC7 "composition law for stage Hom transition"]
theorem stageTransitionHomMap_comp
    (K₀ L₀ : DerivedCategory (ModuleCat (F.obj i₀)))
    {j k l : Set.Ici i₀} (f : j ⟶ k) (g : k ⟶ l) :
    TypeCat.ofHom (stageTransitionHomMap F i₀ K₀ L₀ (f ≫ g)) =
      TypeCat.ofHom (stageTransitionHomMap F i₀ K₀ L₀ f) ≫
        TypeCat.ofHom (stageTransitionHomMap F i₀ K₀ L₀ g) := sorry

/-- The stage Hom functor on the tail `. -/
@[stacks 0BC7 "stage Hom functor"]
noncomputable def stageHomFunctor
    (K₀ L₀ : DerivedCategory (ModuleCat (F.obj i₀))) :
    Set.Ici i₀ ⥤ Type _ where
  obj j := stageHom F i₀ K₀ L₀ j
  map f := TypeCat.ofHom (stageTransitionHomMap F i₀ K₀ L₀ f)
  map_id j := stageTransitionHomMap_id F i₀ K₀ L₀ j
  map_comp f g := stageTransitionHomMap_comp F i₀ K₀ L₀ f g

/-- The target Hom-set after extending both source objects to the filtered colimit. -/
@[stacks 0BC7 "colimit Hom type"]
noncomputable abbrev colimitHom
    (K₀ L₀ : DerivedCategory (ModuleCat (F.obj i₀))) : Type _ :=
  (colimitBaseChange F i₀).obj K₀ ⟶ (colimitBaseChange F i₀).obj L₀

/-- Naturality in the exact bundled form required by the filtered Hom diagram. -/
@[stacks 0BC7 "bundled stage-to-colimit Hom naturality"]
theorem homDiagram_natural
    (K₀ L₀ : DerivedCategory (ModuleCat (F.obj i₀))) :
    ∀ {j k : Set.Ici i₀} (f : j ⟶ k)
      (β : (stageHomFunctor F i₀ K₀ L₀).obj j),
      stageToColimitHomMap F i₀ K₀ L₀ k
          ((stageHomFunctor F i₀ K₀ L₀).map f β) =
        stageToColimitHomMap F i₀ K₀ L₀ j β := sorry

/-- The explicit filtered Hom diagram attached to two source objects. -/
@[stacks 0BC7 "filtered Hom diagram"]
noncomputable def homDiagram
    (K₀ L₀ : DerivedCategory (ModuleCat (F.obj i₀))) :
    CategoryTheory.DerivedCategory.FilteredColimit.HomDiagram
      (stageHomFunctor F i₀ K₀ L₀) (colimitHom F i₀ K₀ L₀) :=
  { ι := stageToColimitHomMap F i₀ K₀ L₀
    natural := fun {i j} f β ↦
      homDiagram_natural F i₀ K₀ L₀ (j := i) (k := j) f β }

/-- Proposition that the explicit stage Hom diagram is a colimit when the source is perfect. -/
@[stacks 0BC7 "perfect-source Hom colimit"]
theorem homDiagram_isColimit
    (K₀ L₀ : DerivedCategory (ModuleCat (F.obj i₀))) (hK₀ : K₀.IsPerfect) :
    Nonempty (IsColimit (homDiagram F i₀ K₀ L₀).cocone) := sorry

/-- Lemma 15.75.18 (0BC7), Hom factorization: every colimit morphism is represented at a later
stage when the source object is perfect. -/
@[stacks 0BC7 "perfect-source Hom factorization"]
theorem exists_stage_factorization_of_isPerfect
    (K₀ L₀ : DerivedCategory (ModuleCat (F.obj i₀))) (hK₀ : K₀.IsPerfect)
    (α : colimitHom F i₀ K₀ L₀) :
    ∃ (j : Set.Ici i₀) (β : stageHom F i₀ K₀ L₀ j),
      α = stageToColimitHomMap F i₀ K₀ L₀ j β := sorry

/-- Lemma 15.75.18 (0BC7), Hom eventual equality: equal stage representatives become equal at a
later stage when the source object is perfect. -/
@[stacks 0BC7 "perfect-source Hom eventual equality"]
theorem eventually_eq_of_stage_morphisms_with_equal_colimit_images_of_isPerfect
    (K₀ L₀ : DerivedCategory (ModuleCat (F.obj i₀))) (hK₀ : K₀.IsPerfect)
    {j : Set.Ici i₀} (β₁ β₂ : stageHom F i₀ K₀ L₀ j)
    (hβ : stageToColimitHomMap F i₀ K₀ L₀ j β₁ =
      stageToColimitHomMap F i₀ K₀ L₀ j β₂) :
    ∃ (k : Set.Ici i₀) (hjk : j ⟶ k),
      stageTransitionHomMap F i₀ K₀ L₀ hjk β₁ =
        stageTransitionHomMap F i₀ K₀ L₀ hjk β₂ := sorry

end Hom

end CategoryTheory.DerivedCategory.Perfect.FilteredColimit
