module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Filtration.Complex.StageSequence

/-!
# Negative filtration stages as a sequential diagram

This is the negative-integer specialization of
`FilteredComplex.StageSequence`.  It records the short names and component
formulas used by truncation towers without duplicating the generic sequence
machinery.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex.NegStage

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A]

/-- The filtration index used at stage `n` of the negative-stage diagram. -/
abbrev index (n : ℕ) : ℤ := -(n : ℤ)

/-- Negative-stage indices reverse the order on natural numbers. -/
theorem index_anti : Antitone index := sorry

/-- The `n`th negative filtration stage of a filtered complex. -/
abbrev obj (K : FilteredComplex A) (n : ℕ) : CochainComplex A ℤ :=
  K.stage (index n)

/-- The canonical map from the `n`th negative stage to the next one. -/
@[stacks 0D8Z]
noncomputable abbrev step (K : FilteredComplex A) (n : ℕ) :
    obj K n ⟶ obj K (n + 1) :=
  K.stageComparison (index_anti (Nat.le_succ n))

/-- The degree component of a negative-stage successor map is the corresponding filtration
inclusion. -/
@[simp, stacks 0D8Z]
theorem step_f (K : FilteredComplex A) (n : ℕ) (i : ℤ) :
    (step K n).f i =
      (K.X i).filtration.inclusion (index_anti (Nat.le_succ n)) := sorry

/-- The sequential diagram of negative filtration stages. -/
@[stacks 0D8Z]
noncomputable abbrev diagram (K : FilteredComplex A) : ℕ ⥤ CochainComplex A ℤ :=
  StageSequence.ofAntitone K index index_anti

/-- Evaluating the negative-stage diagram at `n` gives the `n`th stage. -/
@[simp, stacks 0D8Z]
theorem diagram_obj (K : FilteredComplex A) (n : ℕ) :
    (diagram K).obj n = obj K n := sorry

/-- The successor map of the negative-stage diagram is its declared stage comparison. -/
@[simp, stacks 0D8Z]
theorem diagram_step (K : FilteredComplex A) (n : ℕ) :
    (diagram K).map (homOfLE (Nat.le_succ n)) = step K n := sorry

/-- Every map in the negative-stage diagram is the direct comparison between the corresponding
filtration stages. -/
@[stacks 0D8Z]
theorem diagram_map (K : FilteredComplex A) {m n : ℕ} (h : m ≤ n) :
    (diagram K).map (homOfLE h) = K.stageComparison (index_anti h) := sorry

/-- The inclusion of the `n`th negative stage into the underlying complex. -/
@[stacks 0D8Z]
noncomputable abbrev ι (K : FilteredComplex A) (n : ℕ) :
    obj K n ⟶ K.underlying :=
  K.stageInclusion (index n)

/-- A component of the negative-stage inclusion is the corresponding stage-to-underlying map. -/
@[simp, stacks 0D8Z]
theorem ι_f (K : FilteredComplex A) (n : ℕ) (i : ℤ) :
    (ι K n).f i = (FilteredObject.Stage.toForget (index n)).app (K.X i) := sorry

/-- Every transition in the negative-stage diagram is compatible with the inclusions into the
underlying complex. -/
@[reassoc (attr := simp), stacks 0D8Z]
theorem diagram_map_comp_ι (K : FilteredComplex A) {m n : ℕ} (h : m ≤ n) :
    (diagram K).map (homOfLE h) ≫ ι K n = ι K m := sorry

/-- The canonical transformation from the negative-stage diagram to the constant underlying
complex. -/
@[stacks 0D8Z]
noncomputable abbrev toConst (K : FilteredComplex A) :
    diagram K ⟶ (Functor.const ℕ).obj K.underlying :=
  StageSequence.toUnderlying K index index_anti

/-- A component of the canonical transformation is the corresponding stage inclusion. -/
@[simp, stacks 0D8Z]
theorem toConst_app (K : FilteredComplex A) (n : ℕ) :
    (toConst K).app n = ι K n := sorry

/-- The canonical cocone from the negative filtration stages to the underlying complex. -/
@[stacks 0D8Z]
noncomputable abbrev cocone (K : FilteredComplex A) : Cocone (diagram K) :=
  StageSequence.cocone K index index_anti

/-- The point of the negative-stage cocone is the underlying complex. -/
@[simp, stacks 0D8Z]
theorem cocone_pt (K : FilteredComplex A) : (cocone K).pt = K.underlying := sorry

/-- The map between negative stages induced by a morphism of filtered complexes. -/
noncomputable abbrev mapApp {K L : FilteredComplex A} (f : K ⟶ L) (n : ℕ) :
    obj K n ⟶ obj L n :=
  K.stageMap f (index n)

/-- The degree component of `mapApp` is the corresponding map on filtration stages. -/
@[simp]
theorem mapApp_f {K L : FilteredComplex A} (f : K ⟶ L) (n : ℕ) (i : ℤ) :
    (mapApp f n).f i = (f.f i).stageMap (index n) := sorry

/-- A morphism of filtered complexes induces a natural transformation between its negative-stage
diagrams. -/
@[stacks 0D8Z]
noncomputable abbrev map {K L : FilteredComplex A} (f : K ⟶ L) :
    diagram K ⟶ diagram L :=
  StageSequence.map f index index_anti

/-- The component of the induced map of negative-stage diagrams is the corresponding stage map. -/
@[simp, stacks 0D8Z]
theorem map_app {K L : FilteredComplex A} (f : K ⟶ L) (n : ℕ) :
    (map f).app n = mapApp f n := sorry

/-- Taking the sequential diagram of negative stages is functorial in the filtered complex. -/
@[stacks 0D8Z]
noncomputable abbrev functor : FilteredComplex A ⥤ (ℕ ⥤ CochainComplex A ℤ) :=
  StageSequence.functor index index_anti

/-- Evaluating the negative-stage functor gives the negative-stage diagram. -/
@[simp, stacks 0D8Z]
theorem functor_obj (K : FilteredComplex A) :
    (functor (A := A)).obj K = diagram K := sorry

/-- The map of the negative-stage functor is the canonical map of stage diagrams. -/
@[simp, stacks 0D8Z]
theorem functor_map {K L : FilteredComplex A} (f : K ⟶ L) :
    (functor (A := A)).map f = map f := sorry

/-- Stage maps commute with the inclusions into the underlying complexes. -/
@[reassoc, stacks 0D8Z]
theorem mapApp_comp_ι {K L : FilteredComplex A} (f : K ⟶ L) (n : ℕ) :
    mapApp f n ≫ ι L n = ι K n ≫ K.underlyingMap f := sorry

/-- The map of negative-stage diagrams is compatible with the canonical transformations to the
underlying complexes. -/
@[stacks 0D8Z]
theorem map_comp_toConst {K L : FilteredComplex A} (f : K ⟶ L) :
    map f ≫ toConst L =
      toConst K ≫ (Functor.const ℕ).map (K.underlyingMap f) := sorry

end CategoryTheory.FilteredComplex.NegStage
