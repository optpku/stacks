module

public import Mathlib.CategoryTheory.Sites.Limits
public import ReasLib.CategoryTheory.MorphismProperty.OrdinalSmall
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.FunctorialInjectives
public import ReasLib.CategoryTheory.SmallObject.BoundedIteration

@[expose] public section

open CategoryTheory Limits
open CategoryTheory.SmallObject

universe wI w v u

namespace CategoryTheory.AbelianSheaf.InjectiveTower

noncomputable section

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C)
variable [HasWeakSheafify K AddCommGrpCat.{max u v}]
variable [HasFunctorialInjectives AddCommGrpCat.{max u v}]
variable [UnivLE.{w, max u v}]

/-- The chosen injective-target endofunctor on abelian presheaves. -/
@[stacks 01DK "presheaf injective-target functor"]
noncomputable abbrev presheafJ :
    (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) :=
  AbelianPresheaf.injectiveFunctor C

/-- The chosen natural monomorphism from an abelian presheaf to its injective target. -/
@[stacks 01DK "presheaf functorial injective embedding"]
noncomputable abbrev presheafι :
    𝟭 (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⟶ presheafJ :=
  AbelianPresheaf.injectiveι C

/-- The one-step injective enlargement functor on abelian sheaves. -/
noncomputable abbrev oneFunctor :
    Sheaf K AddCommGrpCat.{max u v} ⥤ Sheaf K AddCommGrpCat.{max u v} :=
  sheafToPresheaf K AddCommGrpCat.{max u v} ⋙ presheafJ ⋙
    presheafToSheaf K AddCommGrpCat.{max u v}

/-- The natural one-step map from an abelian sheaf to its injective enlargement. -/
@[stacks 01DM "one-step injective enlargement map"]
noncomputable def oneMap :
    𝟭 (Sheaf K AddCommGrpCat.{max u v}) ⟶ oneFunctor K :=
  (sheafificationNatIso K AddCommGrpCat.{max u v}).hom ≫
    Functor.whiskerRight
      (Functor.whiskerLeft
        (sheafToPresheaf K AddCommGrpCat.{max u v}) presheafι)
      (presheafToSheaf K AddCommGrpCat.{max u v})

/-- The one-step injective enlargement of an abelian sheaf. -/
noncomputable abbrev one (F : Sheaf K AddCommGrpCat.{max u v}) :
    Sheaf K AddCommGrpCat.{max u v} :=
  (oneFunctor K).obj F

/-- The component of the natural one-step enlargement map. -/
noncomputable abbrev ι (F : Sheaf K AddCommGrpCat.{max u v}) :
    F ⟶ one K F :=
  (oneMap K).app F

/-- Each component of the natural one-step enlargement map is a monomorphism. -/
@[stacks 01DM "monomorphic one-step injective enlargement"]
theorem mono_oneMap_app (F : Sheaf K AddCommGrpCat.{max u v}) :
    Mono (ι K F) := sorry

attribute [instance] mono_oneMap_app

/-- The natural one-step enlargement map is a monomorphism in the endofunctor category. -/
@[stacks 01DM "monomorphic one-step injective enlargement", instance]
theorem mono_oneMap : Mono (oneMap K) := sorry

/-- The successor structure whose transfinite iteration produces the injective tower of `F`. -/
noncomputable def succStruct (F : Sheaf K AddCommGrpCat.{max u v}) :
    SuccStruct (Sheaf K AddCommGrpCat.{max u v}) where
  X₀ := F
  succ := one K
  toSucc := ι K

/-- The closed ordinal interval indexing the tower with top `β`. -/
abbrev Shape (β : Ordinal.{w}) := SmallObject.SuccStruct.OrdinalBounded.Shape β

/-- The bounded injective-tower diagram ending at `β`. -/
noncomputable abbrev diagram (β : Ordinal.{w})
    (F : Sheaf K AddCommGrpCat.{max u v}) :
    Shape β ⥤ Sheaf K AddCommGrpCat.{max u v} :=
  SmallObject.SuccStruct.OrdinalBounded.diagram (succStruct K F) β

/-- The `α`-stage inside the bounded injective tower ending at `β`. -/
noncomputable abbrev stage {α β : Ordinal.{w}} (h : α ≤ β)
    (F : Sheaf K AddCommGrpCat.{max u v}) :
    Sheaf K AddCommGrpCat.{max u v} :=
  SmallObject.SuccStruct.OrdinalBounded.obj (succStruct K F) h

/-- The top object `J_β(F)` of the bounded injective tower ending at `β`. -/
@[stacks 01DM "bounded injective tower"]
noncomputable abbrev J (β : Ordinal.{w}) (F : Sheaf K AddCommGrpCat.{max u v}) :
    Sheaf K AddCommGrpCat.{max u v} :=
  SmallObject.SuccStruct.OrdinalBounded.top (succStruct K F) β

/-- The canonical map between two stages of the same bounded injective tower. -/
@[stacks 01DN "bounded injective-tower transition"]
noncomputable def map {α₁ α₂ β : Ordinal.{w}} (h₁ : α₁ ≤ β) (h₂ : α₂ ≤ β)
    (h₁₂ : α₁ ≤ α₂) (F : Sheaf K AddCommGrpCat.{max u v}) :
    stage K h₁ F ⟶ stage K h₂ F :=
  SmallObject.SuccStruct.OrdinalBounded.map (succStruct K F) h₁ h₂ h₁₂

/-- Every transition map in a bounded injective tower is a monomorphism. -/
@[stacks 01DN "monomorphic bounded-tower transition"]
theorem mono_map {α₁ α₂ β : Ordinal.{w}} (h₁ : α₁ ≤ β) (h₂ : α₂ ≤ β)
    (h₁₂ : α₁ ≤ α₂) (F : Sheaf K AddCommGrpCat.{max u v}) :
    Mono (map K h₁ h₂ h₁₂ F) := sorry

attribute [instance] mono_map

/-- The canonical map from a stage to the top of the same bounded injective tower. -/
@[stacks 01DN "bounded injective-tower map to the top"]
noncomputable def toTop {α β : Ordinal.{w}} (h : α ≤ β)
    (F : Sheaf K AddCommGrpCat.{max u v}) :
    stage K h F ⟶ J K β F :=
  SmallObject.SuccStruct.OrdinalBounded.toTop (succStruct K F) h

/-- Every canonical map to the top of a bounded injective tower is a monomorphism. -/
@[stacks 01DN "monomorphic map to the tower top"]
theorem mono_toTop {α β : Ordinal.{w}} (h : α ≤ β)
    (F : Sheaf K AddCommGrpCat.{max u v}) :
    Mono (toTop K h F) := sorry

attribute [instance] mono_toTop

/-- The type of ordinal stages strictly below `β`. -/
abbrev Below (β : Ordinal.{w}) := Set.Iio β

/-- The stage selected by `α < β` inside the single bounded tower ending at `β`. -/
noncomputable abbrev belowStage {β : Ordinal.{w}} (α : Below β)
    (F : Sheaf K AddCommGrpCat.{max u v}) :
    Sheaf K AddCommGrpCat.{max u v} :=
  stage K α.property.le F

/-- The canonical map from a stage strictly below `β` to the top of that same bounded tower. -/
noncomputable def belowToTop {β : Ordinal.{w}} (α : Below β)
    (F : Sheaf K AddCommGrpCat.{max u v}) :
    belowStage K α F ⟶ J K β F :=
  toTop K α.property.le F

/-- The canonical map from a stage strictly below the top of a bounded injective tower is a
monomorphism. -/
theorem mono_belowToTop {β : Ordinal.{w}} (α : Below β)
    (F : Sheaf K AddCommGrpCat.{max u v}) :
    Mono (belowToTop K α F) := sorry

attribute [instance] mono_belowToTop

/-- The index immediately after `α < β` in the single bounded diagram ending at `β`. -/
noncomputable abbrev nextIndex {β : Ordinal.{w}} (α : Below β) : Shape β :=
  Order.succ (SmallObject.SuccStruct.OrdinalBounded.index α.property.le)

omit [HasFunctorialInjectives AddCommGrpCat.{max u v}]
  [UnivLE.{w, max u v}] in
/-- The index selected by `α < β` is not maximal in the bounded tower ending at `β`. -/
@[stacks 01DM "successor index below the tower top"]
theorem not_isMax_index {β : Ordinal.{w}} (α : Below β) :
    ¬ IsMax (SmallObject.SuccStruct.OrdinalBounded.index α.property.le) := sorry

/-- The stage immediately after `α < β` in the single bounded injective tower ending at
`β`. -/
@[stacks 01DM "successor stage in a fixed bounded tower"]
noncomputable abbrev nextStage {β : Ordinal.{w}} (α : Below β)
    (F : Sheaf K AddCommGrpCat.{max u v}) :
    Sheaf K AddCommGrpCat.{max u v} :=
  (diagram K β F).obj (nextIndex α)

/-- The canonical successor map after `α < β`, formed inside the single bounded diagram
ending at `β`. -/
@[stacks 01DM "successor map in a fixed bounded tower"]
noncomputable def belowToNext {β : Ordinal.{w}} (α : Below β)
    (F : Sheaf K AddCommGrpCat.{max u v}) :
    belowStage K α F ⟶ nextStage K α F :=
  (diagram K β F).map (homOfLE (Order.le_succ _))

/-- The successor map inside a fixed bounded injective tower is a monomorphism. -/
theorem mono_belowToNext {β : Ordinal.{w}} (α : Below β)
    (F : Sheaf K AddCommGrpCat.{max u v}) :
    Mono (belowToNext K α F) := sorry

attribute [instance] mono_belowToNext

/-- The canonical identification of the stage after `α < β` with the one-step injective
enlargement of the `α`-stage in that same bounded tower. -/
@[stacks 01DM "successor-stage comparison in a fixed bounded tower"]
noncomputable def nextIso {β : Ordinal.{w}} (α : Below β)
    (F : Sheaf K AddCommGrpCat.{max u v}) :
    nextStage K α F ≅ one K (belowStage K α F) :=
  (succStruct K F).iterationFunctorObjSuccIso
    (SmallObject.SuccStruct.OrdinalBounded.index α.property.le)
    (not_isMax_index α)

/-- The canonical map from the stage after `α < β` to the top of the same bounded tower. -/
@[stacks 01DM "successor-stage map to the top"]
noncomputable def nextToTop {β : Ordinal.{w}} (α : Below β)
    (F : Sheaf K AddCommGrpCat.{max u v}) :
    nextStage K α F ⟶ J K β F :=
  (diagram K β F).map
    (homOfLE
      (show nextIndex α ≤
          SmallObject.SuccStruct.OrdinalBounded.index (le_rfl : β ≤ β)
        from le_top))

/-- The canonical map from a successor stage to the top of its fixed bounded tower is a
monomorphism. -/
theorem mono_nextToTop {β : Ordinal.{w}} (α : Below β)
    (F : Sheaf K AddCommGrpCat.{max u v}) :
    Mono (nextToTop K α F) := sorry

attribute [instance] mono_nextToTop

/-- Passing first to the next stage and then to the top agrees with the direct map to the top. -/
@[stacks 01DM "successor-stage composition to the top"]
theorem belowToNext_comp_nextToTop {β : Ordinal.{w}} (α : Below β)
    (F : Sheaf K AddCommGrpCat.{max u v}) :
    belowToNext K α F ≫ nextToTop K α F = belowToTop K α F := sorry

/-- Under `nextIso`, the successor transition in the bounded tower is the one-step enlargement
map. -/
theorem belowToNext_comp_nextIso_hom {β : Ordinal.{w}} (α : Below β)
    (F : Sheaf K AddCommGrpCat.{max u v}) :
    belowToNext K α F ≫ (nextIso K α F).hom = ι K (belowStage K α F) := sorry

/-- A chosen factorization of a fixed map to the top of a bounded injective tower through a
stage strictly below the top. -/
@[stacks 01DN "factorization below the top of an injective tower"]
structure Factorization {β : Ordinal.{w}}
    {G F : Sheaf K AddCommGrpCat.{max u v}} (φ : G ⟶ J K β F) where
  /-- The stage strictly below the top through which the map factors. -/
  α : Below β
  /-- The map to the selected stage. -/
  hom : G ⟶ belowStage K α F
  /-- Composing the selected map with the canonical map to the top recovers the fixed map. -/
  fac : hom ≫ belowToTop K α F = φ

/-- A chosen lift to the successor of a fixed stage across a morphism of sources.  Monicity is
required only by existence theorems, not by this data structure. -/
@[stacks 01DM "successor-stage lift"]
structure SuccessorLift {β : Ordinal.{w}} (α : Below β)
    {G₁ G₂ F : Sheaf K AddCommGrpCat.{max u v}}
    (i : G₁ ⟶ G₂) (f : G₁ ⟶ belowStage K α F) where
  /-- The lifted map from the enlarged source to the successor stage. -/
  hom : G₂ ⟶ nextStage K α F
  /-- The square formed by the source map and the successor transition commutes. -/
  commSq : CommSq f i (belowToNext K α F) hom

/-- A successor lift of a factorization still recovers its fixed map after composition to the
top of the bounded tower. -/
@[stacks 01DN "successor lift composed to the tower top"]
theorem Factorization.top
    {β : Ordinal.{w}} {G₁ G₂ F : Sheaf K AddCommGrpCat.{max u v}}
    {φ : G₁ ⟶ J K β F} (e : Factorization K φ) {i : G₁ ⟶ G₂}
    (l : SuccessorLift K e.α i e.hom) :
    i ≫ l.hom ≫ nextToTop K e.α F = φ := sorry

/-- Lemma 19.7.1: every map into a stage strictly below the top extends across a monomorphism
after passing to the next stage of that same bounded injective tower. -/
@[stacks 01DM "successor-stage lifting in a fixed bounded tower"]
theorem existsLift
    {β : Ordinal.{w}} (α : Below β)
    {G₁ G₂ F : Sheaf K AddCommGrpCat.{max u v}}
    (i : G₁ ⟶ G₂) [Mono i] (f : G₁ ⟶ belowStage K α F) :
    Nonempty (SuccessorLift K α i f) := sorry

/-- An ordinal uniformly bounds a family when every map from that family to the top of the
bounded injective tower has a factorization through a strictly earlier stage. -/
@[stacks 01DN "uniform factorization bound"]
def IsBound {I : Type wI} (G : I → Sheaf K AddCommGrpCat.{max u v})
    (β : Ordinal.{w}) : Prop :=
  ∀ (F : Sheaf K AddCommGrpCat.{max u v}) (i : I) (φ : G i ⟶ J K β F),
    Nonempty (Factorization K φ)

/-- Apply a uniform bound to a fixed target sheaf, family member, and map to the tower top. -/
@[stacks 01DN "apply a uniform factorization bound"]
theorem IsBound.apply
    {I : Type wI} {G : I → Sheaf K AddCommGrpCat.{max u v}} {β : Ordinal.{w}}
    (h : IsBound K G β) (F : Sheaf K AddCommGrpCat.{max u v}) (i : I)
    (φ : G i ⟶ J K β F) :
    Nonempty (Factorization K φ) := sorry

/-- A factorization supplied by a uniform bound admits a successor-stage lift across any
monomorphism from its source. -/
@[stacks 01DN "successor lifting at a uniform factorization bound"]
theorem IsBound.existsLift
    {I : Type wI} {G : I → Sheaf K AddCommGrpCat.{max u v}} {β : Ordinal.{w}}
    (h : IsBound K G β) (F : Sheaf K AddCommGrpCat.{max u v}) (i : I)
    (φ : G i ⟶ J K β F) {G₂ : Sheaf K AddCommGrpCat.{max u v}}
    (m : G i ⟶ G₂) [Mono m] :
    ∃ e : Factorization K φ,
      Nonempty (SuccessorLift K e.α m e.hom) := sorry

/-- A small family of abelian sheaves has a common ordinal-smallness bound with respect to
monomorphisms. -/
@[stacks 01DN "common ordinal-smallness bound"]
theorem existsSmallnessBound
    {I : Type wI} [Small.{w} I] (G : I → Sheaf K AddCommGrpCat.{max u v}) :
    ∃ β : Ordinal.{w}, Order.IsSuccLimit β ∧
      ∀ i, (MorphismProperty.monomorphisms _).IsOrdinalSmall (G i) β := sorry

/-- A small family admits a successor-limit ordinal which is a uniform factorization bound. -/
@[stacks 01DN "successor-limit uniform factorization bound"]
theorem existsSuccLimitBound
    {I : Type wI} [Small.{w} I] (G : I → Sheaf K AddCommGrpCat.{max u v}) :
    ∃ β : Ordinal.{w}, Order.IsSuccLimit β ∧ IsBound K G β := sorry

/-- Lemma 19.7.2: a small family admits one ordinal stage at which every map into the top of the
injective tower factors through a strictly earlier stage of the same bounded tower. -/
@[stacks 01DN]
theorem existsBound
    {I : Type wI} [Small.{w} I] (G : I → Sheaf K AddCommGrpCat.{max u v}) :
    ∃ β : Ordinal.{w}, IsBound K G β := sorry

#synth HasColimitsOfSize.{w, w} (Sheaf K AddCommGrpCat.{max u v})

end

end CategoryTheory.AbelianSheaf.InjectiveTower
