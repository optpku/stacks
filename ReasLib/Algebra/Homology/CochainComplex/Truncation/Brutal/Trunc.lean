module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import ReasLib.Algebra.Homology.CochainComplex.Truncation.Brutal

/-!
# The brutal tower in the `stupidTrunc` model

This leaf transports the canonical stupid-filtration tower across
`Brutal.Stage.truncIso`.  It gives applications that already use mathlib's
`HomologicalComplex.stupidTrunc` an explicit stage, transition, inclusion,
diagram, and cocone API without reconstructing components by hand.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

universe v u

namespace CategoryTheory.CochainComplex.Brutal.Trunc

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The `n`th brutal stage in mathlib's `stupidTrunc` model. -/
@[stacks 0D8Z]
noncomputable abbrev obj (K : CochainComplex A ℤ) (n : ℕ) : CochainComplex A ℤ :=
  K.stupidTrunc (embeddingUpIntGE (Tower.index n))

/-- The canonical comparison from the filtration-stage model to the `stupidTrunc` model. -/
@[stacks 0D8Z]
noncomputable abbrev stageIso (K : CochainComplex A ℤ) (n : ℕ) :
    Tower.obj K n ≅ obj K n :=
  Tower.truncIso K n

/-- The canonical inclusion of a `stupidTrunc` stage into the original complex. -/
@[stacks 0D8Z]
noncomputable def ι (K : CochainComplex A ℤ) (n : ℕ) : obj K n ⟶ K :=
  (stageIso K n).inv ≫ Tower.ι K n

/-- The canonical map between consecutive `stupidTrunc` stages. -/
@[stacks 0D8Z]
noncomputable def step (K : CochainComplex A ℤ) (n : ℕ) :
    obj K n ⟶ obj K (n + 1) :=
  (stageIso K n).inv ≫ Tower.step K n ≫ (stageIso K (n + 1)).hom

/-- The sequential diagram in the `stupidTrunc` model. -/
@[stacks 0D8Z]
noncomputable def diagram (K : CochainComplex A ℤ) : ℕ ⥤ CochainComplex A ℤ :=
  Functor.ofSequence (step K)

/-- Evaluating the `stupidTrunc` diagram at `n` gives its `n`th stage. -/
@[simp, stacks 0D8Z]
theorem diagram_obj (K : CochainComplex A ℤ) (n : ℕ) :
    (diagram K).obj n = obj K n := sorry

/-- The successor map in the `stupidTrunc` diagram is its declared transported comparison. -/
@[simp, stacks 0D8Z]
theorem diagram_step (K : CochainComplex A ℤ) (n : ℕ) :
    (diagram K).map (homOfLE (Nat.le_add_right n 1)) = step K n := sorry

/-- Consecutive `stupidTrunc` stages are compatible with their inclusions into the original
complex. -/
@[reassoc (attr := simp), stacks 0D8Z]
theorem step_comp_ι (K : CochainComplex A ℤ) (n : ℕ) :
    step K n ≫ ι K (n + 1) = ι K n := sorry

/-- The successor compatibility equation used to form the `stupidTrunc` cocone. -/
@[stacks 0D8Z]
theorem toConst_naturality (K : CochainComplex A ℤ) (n : ℕ) :
    (diagram K).map (homOfLE (Nat.le_add_right n 1)) ≫ ι K (n + 1) =
      ι K n ≫ ((Functor.const ℕ).obj K).map
        (homOfLE (Nat.le_add_right n 1)) := sorry

/-- The canonical transformation from the `stupidTrunc` diagram to the constant original
complex. -/
@[stacks 0D8Z]
noncomputable def toConst (K : CochainComplex A ℤ) :
    diagram K ⟶ (Functor.const ℕ).obj K :=
  NatTrans.ofSequence (ι K) (toConst_naturality K)

/-- A component of the canonical transformation is the corresponding `stupidTrunc`
inclusion. -/
@[simp, stacks 0D8Z]
theorem toConst_app (K : CochainComplex A ℤ) (n : ℕ) :
    (toConst K).app n = ι K n := sorry

/-- The canonical cocone from the sequential `stupidTrunc` diagram to the original complex. -/
@[stacks 0D8Z]
noncomputable def cocone (K : CochainComplex A ℤ) : Cocone (diagram K) :=
  Cocone.mk K (toConst K)

/-- A leg of the canonical cocone is the corresponding `stupidTrunc` inclusion. -/
@[simp, stacks 0D8Z]
theorem cocone_ι_app (K : CochainComplex A ℤ) (n : ℕ) :
    (cocone K).ι.app n = ι K n := sorry

/-- A cochain map induces the termwise map between its `stupidTrunc` stages. -/
noncomputable abbrev mapApp {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℕ) :
    obj K n ⟶ obj L n :=
  HomologicalComplex.stupidTruncMap f (embeddingUpIntGE (Tower.index n))

/-- The transported successor maps are natural in the original cochain complex. -/
@[stacks 0D8Z]
theorem step_naturality {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℕ) :
    step K n ≫ mapApp f (n + 1) = mapApp f n ≫ step L n := sorry

/-- The successor naturality equation in the form expected by `NatTrans.ofSequence`. -/
@[stacks 0D8Z]
theorem map_naturality {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℕ) :
    (diagram K).map (homOfLE (Nat.le_add_right n 1)) ≫ mapApp f (n + 1) =
      mapApp f n ≫ (diagram L).map (homOfLE (Nat.le_add_right n 1)) := sorry

/-- A cochain map induces a natural transformation of `stupidTrunc` diagrams. -/
@[stacks 0D8Z]
noncomputable def map {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    diagram K ⟶ diagram L :=
  NatTrans.ofSequence (mapApp f) (map_naturality f)

/-- The component of a map of `stupidTrunc` diagrams is mathlib's canonical truncation map. -/
@[simp, stacks 0D8Z]
theorem map_app {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℕ) :
    (map f).app n = mapApp f n := sorry

/-- The `stupidTrunc` brutal tower map of an identity is the identity transformation. -/
@[simp, stacks 0D8Z]
theorem map_id (K : CochainComplex A ℤ) : map (𝟙 K) = 𝟙 (diagram K) := sorry

/-- Maps of `stupidTrunc` diagrams preserve composition. -/
@[simp, stacks 0D8Z]
theorem map_comp {K L M : CochainComplex A ℤ} (f : K ⟶ L) (g : L ⟶ M) :
    map (f ≫ g) = map f ≫ map g := sorry

/-- Taking the sequential `stupidTrunc` diagram is functorial in the cochain complex. -/
@[stacks 0D8Z]
noncomputable def functor : CochainComplex A ℤ ⥤ (ℕ ⥤ CochainComplex A ℤ) where
  obj := diagram
  map := map
  map_id := map_id
  map_comp := map_comp

/-- Evaluating the transported truncation functor gives the `stupidTrunc` diagram. -/
@[simp, stacks 0D8Z]
theorem functor_obj (K : CochainComplex A ℤ) :
    (functor (A := A)).obj K = diagram K := sorry

/-- The map of the transported truncation functor is the canonical truncation-diagram map. -/
@[simp, stacks 0D8Z]
theorem functor_map {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    (functor (A := A)).map f = map f := sorry

/-- A `stupidTrunc` stage vanishes strictly below its cutoff. -/
theorem isZero_X (K : CochainComplex A ℤ) (n : ℕ) (i : ℤ) (hi : i < Tower.index n) :
    IsZero ((obj K n).X i) := sorry

/-- On a retained degree, the canonical inclusion is the standard term identification. -/
@[simp, stacks 0D8Z]
theorem ι_f_of_le (K : CochainComplex A ℤ) (n : ℕ) (i : ℤ)
    (hi : Tower.index n ≤ i) :
    (ι K n).f i = (StupidTrunc.activeIso K (Tower.index n) i hi).hom := sorry

/-- Below the cutoff, the canonical inclusion vanishes. -/
@[simp, stacks 0D8Z]
theorem ι_f_of_lt (K : CochainComplex A ℤ) (n : ℕ) (i : ℤ)
    (hi : i < Tower.index n) :
    (ι K n).f i = 0 := sorry

/-- On a degree retained by stage `n`, its inclusion into the original complex is an
isomorphism. -/
theorem ι_f_isIso (K : CochainComplex A ℤ) (n : ℕ) (i : ℤ)
    (hi : Tower.index n ≤ i) : IsIso ((ι K n).f i) := sorry

/-- On a degree retained by stage `n`, the successor map is transported from the identity on the
corresponding term of the original complex. -/
@[stacks 0D8Z]
theorem step_f_of_le (K : CochainComplex A ℤ) (n : ℕ) (i : ℤ)
    (hi : Tower.index n ≤ i) :
    (step K n).f i =
      (StupidTrunc.activeIso K (Tower.index n) i hi).hom ≫
        (StupidTrunc.activeIso K (Tower.index (n + 1)) i
          (FilteredComplex.NegStage.index_anti (Nat.le_add_right n 1) |>.trans hi)).inv := sorry

/-- Below the old cutoff, the successor map vanishes. -/
@[simp, stacks 0D8Z]
theorem step_f_of_lt (K : CochainComplex A ℤ) (n : ℕ) (i : ℤ)
    (hi : i < Tower.index n) :
    (step K n).f i = 0 := sorry

/-- On a degree retained by stage `n`, the successor map is an isomorphism. -/
theorem step_f_isIso (K : CochainComplex A ℤ) (n : ℕ) (i : ℤ)
    (hi : Tower.index n ≤ i) : IsIso ((step K n).f i) := sorry

/-- Maps of `stupidTrunc` diagrams commute with the canonical inclusions into the original
complexes. -/
@[reassoc, stacks 0D8Z]
theorem map_app_comp_ι {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℕ) :
    (map f).app n ≫ ι L n = ι K n ≫ f := sorry

/-- A map of transported truncation diagrams commutes with the transformations to the source
complexes. -/
@[stacks 0D8Z]
theorem map_comp_toConst {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    map f ≫ toConst L = toConst K ≫ (Functor.const ℕ).map f := sorry

namespace ToConst

/-- Naturality of the transported tower-to-constant transformation, stated on the functorial
owner. -/
@[stacks 0D8Z]
theorem naturality {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    (functor (A := A)).map f ≫ toConst L =
      toConst K ≫ (Functor.const ℕ).map f := sorry

end ToConst

/-- The transported truncation inclusions form a natural transformation to the constant-diagram
functor. -/
@[stacks 0D8Z]
noncomputable def toConstNatTrans :
    functor (A := A) ⟶ (Functor.const ℕ : CochainComplex A ℤ ⥤ _) where
  app := toConst
  naturality := fun {K L} f ↦
    ToConst.naturality (A := A) (K := K) (L := L) f

/-- The component of the transported tower-to-constant natural transformation is its canonical
stage transformation. -/
@[simp, stacks 0D8Z]
theorem toConstNatTrans_app (K : CochainComplex A ℤ) :
    (toConstNatTrans (A := A)).app K = toConst K := sorry

end CategoryTheory.CochainComplex.Brutal.Trunc
