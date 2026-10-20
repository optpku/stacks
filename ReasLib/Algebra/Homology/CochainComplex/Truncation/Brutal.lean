/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.CochainComplex.Filtration.Stupid.Functor
public import ReasLib.CategoryTheory.Filtration.Complex.NegStage

/-!
# Brutal truncation stages and towers

The primitive owner of a brutal lower truncation is a stage of the stupid
filtration.  This file specializes the neutral negative-stage diagram and
retains an explicit comparison to mathlib's `HomologicalComplex.stupidTrunc`
model.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

universe v u

namespace CategoryTheory.CochainComplex.Brutal

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace Stage

/-- The brutal lower truncation of `K` retaining degrees at least `p`, modeled as a stage of the
stupid filtration. -/
@[stacks 0D8Z]
abbrev obj (K : CochainComplex A ℤ) (p : ℤ) : CochainComplex A ℤ :=
  K.stupidFiltration.stage p

/-- The canonical map from the `q`-stage to the `p`-stage for `p ≤ q`. -/
@[stacks 0D8Z]
noncomputable abbrev comparison (K : CochainComplex A ℤ) {p q : ℤ} (hpq : p ≤ q) :
    obj K q ⟶ obj K p :=
  K.stupidFiltration.stageComparison hpq

/-- The canonical inclusion of a brutal stage into the original cochain complex. -/
@[stacks 0D8Z]
noncomputable abbrev ι (K : CochainComplex A ℤ) (p : ℤ) : obj K p ⟶ K :=
  K.stupidFiltration.stageInclusion p

/-- A cochain map induces a map between the brutal stages at a fixed cutoff. -/
noncomputable abbrev map {K L : CochainComplex A ℤ} (f : K ⟶ L) (p : ℤ) :
    obj K p ⟶ obj L p :=
  K.stupidFiltration.stageMap (Stupid.map f) p

/-- The degree component of a brutal-stage comparison is the corresponding filtration
inclusion. -/
@[simp]
theorem comparison_f (K : CochainComplex A ℤ) {p q : ℤ} (hpq : p ≤ q) (i : ℤ) :
    (comparison K hpq).f i = (K.stupidFiltration.X i).filtration.inclusion hpq := sorry

/-- The degree component of the stage inclusion is the stupid-filtration subobject inclusion. -/
@[simp]
theorem ι_f (K : CochainComplex A ℤ) (p i : ℤ) :
    (ι K p).f i = (FilteredObject.Stage.toForget p).app (K.stupidFiltration.X i) := sorry

/-- The canonical identification of an active stage term with the corresponding term of `K`. -/
noncomputable abbrev xIso (K : CochainComplex A ℤ) (p i : ℤ) (hpi : p ≤ i) :
    (obj K p).X i ≅ K.X i :=
  StupidFiltration.stageActiveIso K p i hpi

/-- On an active degree, the stage inclusion is the canonical term isomorphism. -/
@[simp, stacks 0D8Z]
theorem xIso_hom (K : CochainComplex A ℤ) (p i : ℤ) (hpi : p ≤ i) :
    (xIso K p i hpi).hom = (ι K p).f i := sorry

/-- A brutal stage vanishes strictly below its cutoff. -/
theorem isZero_X (K : CochainComplex A ℤ) (p i : ℤ) (hip : i < p) :
    IsZero ((obj K p).X i) := sorry

/-- On active degrees, the stage differential identifies with the differential of the original
cochain complex. -/
theorem d_via_xIso (K : CochainComplex A ℤ) (p : ℤ) {i j : ℤ}
    (hpi : p ≤ i) (hpj : p ≤ j) (hij : (ComplexShape.up ℤ).Rel i j) :
    (xIso K p i hpi).inv ≫ (obj K p).d i j ≫ (xIso K p j hpj).hom = K.d i j := sorry

/-- A stage comparison followed by the earlier stage inclusion is the later stage inclusion. -/
@[reassoc (attr := simp), stacks 0D8Z]
theorem comparison_comp_ι (K : CochainComplex A ℤ) {p q : ℤ} (hpq : p ≤ q) :
    comparison K hpq ≫ ι K p = ι K q := sorry

/-- Stage comparisons are natural in the original cochain complex. -/
@[stacks 0D8Z]
theorem comparison_naturality {K L : CochainComplex A ℤ} (f : K ⟶ L)
    {p q : ℤ} (hpq : p ≤ q) :
    comparison K hpq ≫ map f p = map f q ≫ comparison L hpq := sorry

/-- Stage maps commute with the canonical inclusions into the original complexes. -/
@[reassoc, stacks 0D8Z]
theorem map_comp_ι {K L : CochainComplex A ℤ} (f : K ⟶ L) (p : ℤ) :
    map f p ≫ ι L p = ι K p ≫ f := sorry

/-- The filtration-stage model of brutal truncation is canonically isomorphic to mathlib's
`stupidTrunc` model. -/
@[stacks 0D8Z]
noncomputable abbrev truncIso (K : CochainComplex A ℤ) (p : ℤ) :
    obj K p ≅ K.stupidTrunc (embeddingUpIntGE p) :=
  StupidFiltration.stageIso K p

end Stage

namespace Tower

/-- The cutoff of the `n`th brutal truncation stage. -/
abbrev index (n : ℕ) : ℤ := FilteredComplex.NegStage.index n

/-- The `n`th brutal truncation stage, retaining degrees at least `-n`. -/
@[stacks 0D8Z]
abbrev obj (K : CochainComplex A ℤ) (n : ℕ) : CochainComplex A ℤ :=
  FilteredComplex.NegStage.obj K.stupidFiltration n

/-- The inclusion from the `n`th brutal stage into the next one. -/
@[stacks 0D8Z]
noncomputable abbrev step (K : CochainComplex A ℤ) (n : ℕ) :
    obj K n ⟶ obj K (n + 1) :=
  FilteredComplex.NegStage.step K.stupidFiltration n

/-- The sequential diagram of brutal stages of a cochain complex. -/
@[stacks 0D8Z]
noncomputable abbrev diagram (K : CochainComplex A ℤ) : ℕ ⥤ CochainComplex A ℤ :=
  FilteredComplex.NegStage.diagram K.stupidFiltration

/-- Evaluating the brutal-stage diagram at `n` gives its `n`th stage. -/
@[simp, stacks 0D8Z]
theorem diagram_obj (K : CochainComplex A ℤ) (n : ℕ) :
    (diagram K).obj n = obj K n := sorry

/-- The successor map of the brutal-stage diagram is its declared stage inclusion. -/
@[simp, stacks 0D8Z]
theorem diagram_step (K : CochainComplex A ℤ) (n : ℕ) :
    (diagram K).map (homOfLE (Nat.le_succ n)) = step K n := sorry

/-- The inclusion of a brutal tower stage into the original complex. -/
@[stacks 0D8Z]
noncomputable abbrev ι (K : CochainComplex A ℤ) (n : ℕ) : obj K n ⟶ K :=
  FilteredComplex.NegStage.ι K.stupidFiltration n

/-- A cochain map induces a natural transformation between its brutal-stage diagrams. -/
@[stacks 0D8Z]
noncomputable abbrev map {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    diagram K ⟶ diagram L :=
  FilteredComplex.NegStage.map (Stupid.map f)

/-- Taking the sequential brutal-stage diagram is functorial in the cochain complex. -/
@[stacks 0D8Z]
noncomputable def functor : CochainComplex A ℤ ⥤ (ℕ ⥤ CochainComplex A ℤ) :=
  Stupid.functor ⋙ FilteredComplex.NegStage.functor

/-- Evaluating the brutal-tower functor gives the brutal-stage diagram. -/
@[simp, stacks 0D8Z]
theorem functor_obj (K : CochainComplex A ℤ) :
    (functor (A := A)).obj K = diagram K := sorry

/-- The map of the brutal-tower functor is the canonical map of brutal-stage diagrams. -/
@[simp, stacks 0D8Z]
theorem functor_map {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    (functor (A := A)).map f = map f := sorry

/-- The canonical transformation from the brutal-stage diagram to the constant original
complex. -/
@[stacks 0D8Z]
noncomputable abbrev toConst (K : CochainComplex A ℤ) :
    diagram K ⟶ (Functor.const ℕ).obj K :=
  FilteredComplex.NegStage.toConst K.stupidFiltration

/-- A component of the canonical transformation is the corresponding brutal-stage inclusion. -/
@[simp, stacks 0D8Z]
theorem toConst_app (K : CochainComplex A ℤ) (n : ℕ) :
    (toConst K).app n = ι K n := sorry

/-- The canonical cocone from the brutal stages to the original complex. -/
@[stacks 0D8Z]
noncomputable abbrev cocone (K : CochainComplex A ℤ) : Cocone (diagram K) :=
  FilteredComplex.NegStage.cocone K.stupidFiltration

/-- A leg of the canonical cocone is the corresponding brutal-stage inclusion. -/
@[simp, stacks 0D8Z]
theorem cocone_ι_app (K : CochainComplex A ℤ) (n : ℕ) :
    (cocone K).ι.app n = ι K n := sorry

/-- The successor map of the brutal tower is compatible with the stage inclusions. -/
@[reassoc (attr := simp), stacks 0D8Z]
theorem step_comp_ι (K : CochainComplex A ℤ) (n : ℕ) :
    step K n ≫ ι K (n + 1) = ι K n := sorry

/-- A component of the map of brutal towers is the stage map of the stupidly filtered cochain
map. -/
@[simp, stacks 0D8Z]
theorem map_app {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℕ) :
    (map f).app n = Stage.map f (index n) := sorry

/-- Maps of brutal towers commute with the canonical inclusions into the original complexes. -/
@[reassoc, stacks 0D8Z]
theorem map_app_comp_ι {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℕ) :
    (map f).app n ≫ ι L n = ι K n ≫ f := sorry

/-- A map of brutal towers commutes with the canonical transformations to the source
complexes. -/
@[stacks 0D8Z]
theorem map_comp_toConst {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    map f ≫ toConst L = toConst K ≫ (Functor.const ℕ).map f := sorry

namespace ToConst

/-- Naturality of the canonical tower-to-constant transformation, stated on the functorial
owner. -/
@[stacks 0D8Z]
theorem naturality {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    (functor (A := A)).map f ≫ toConst L =
      toConst K ≫ (Functor.const ℕ).map f := sorry

end ToConst

/-- The inclusions of brutal stages form a natural transformation from the tower functor to the
constant-diagram functor. -/
@[stacks 0D8Z]
noncomputable def toConstNatTrans :
    functor (A := A) ⟶ (Functor.const ℕ : CochainComplex A ℤ ⥤ _) where
  app := toConst
  naturality := fun {K L} f ↦
    ToConst.naturality (A := A) (K := K) (L := L) f

/-- The component of the tower-to-constant natural transformation is the canonical stage
transformation. -/
@[simp, stacks 0D8Z]
theorem toConstNatTrans_app (K : CochainComplex A ℤ) :
    (toConstNatTrans (A := A)).app K = toConst K := sorry

/-- The `n`th filtration-stage model is canonically isomorphic to mathlib's stupid truncation at
the same cutoff. -/
@[stacks 0D8Z]
noncomputable abbrev truncIso (K : CochainComplex A ℤ) (n : ℕ) :
    obj K n ≅ K.stupidTrunc (embeddingUpIntGE (index n)) :=
  Stage.truncIso K (index n)

end Tower

end CategoryTheory.CochainComplex.Brutal
