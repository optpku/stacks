/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Degreewise Split Short Complexes

This file contains facts that are independent of the orientation of a homological complex:
degreewise evaluation and the algebra of changing a splitting.
-/

@[expose] public section

open CategoryTheory HomologicalComplex

universe v u

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {ι : Type*} {c : ComplexShape ι}

/-- The short complex obtained by evaluating a short complex of homological complexes in one
degree. -/
abbrev degreewise (S : ShortComplex (HomologicalComplex C c)) (i : ι) : ShortComplex C :=
  S.map (eval C c i)

/-- A chosen splitting in every degree of a short complex of homological complexes. Unlike
`IsDegreewiseSplit`, this is explicit data and can be used to construct connecting maps. -/
@[stacks 014I "chosen degreewise splitting"]
abbrev DegreewiseSplitting (S : ShortComplex (HomologicalComplex C c)) :=
  ∀ i : ι, (S.degreewise i).Splitting

/-- A short complex of homological complexes is degreewise split when every evaluated short
complex admits a splitting.  This is an existence property: it does not choose a splitting. -/
@[stacks 014I "degreewise-split short-complex property"]
def IsDegreewiseSplit (S : ShortComplex (HomologicalComplex C c)) : Prop :=
  ∀ i : ι, Nonempty (S.degreewise i).Splitting

/-- A degreewise-split short complex admits a chosen family of splittings, and conversely. -/
@[stacks 014I "degreewise-splitting family bridge"]
theorem isDegreewiseSplit_iff (S : ShortComplex (HomologicalComplex C c)) :
    S.IsDegreewiseSplit ↔ Nonempty (DegreewiseSplitting S) := sorry

/-- A chosen family of splittings witnesses the degreewise-split property. -/
@[stacks 014I "chosen splitting witnesses degreewise splitness"]
theorem isDegreewiseSplit_of_splitting
    (S : ShortComplex (HomologicalComplex C c))
    (σ : DegreewiseSplitting S) :
    S.IsDegreewiseSplit := sorry

namespace Splitting

variable {S : ShortComplex C}

/-- The splitting `σ'` is obtained from `σ` by adding `h ≫ S.f` to its section. -/
def IsSectionCorrection (σ σ' : S.Splitting) (h : S.X₃ ⟶ S.X₁) : Prop :=
  σ'.s = σ.s + h ≫ S.f

/-- A correction of the section by `h ≫ S.f` corrects the retraction by `-S.g ≫ h`. -/
theorem retraction_eq_sub (σ σ' : S.Splitting) (h : S.X₃ ⟶ S.X₁)
    (hs : σ.IsSectionCorrection σ' h) :
    σ'.r = σ.r - S.g ≫ h := sorry

/-- If section and retraction corrections are written using `h` and `k`, respectively, then
`k = -h`. -/
@[stacks 011L]
theorem retractionCorrection_eq_neg
    (σ σ' : S.Splitting) (h k : S.X₃ ⟶ S.X₁)
    (hs : σ.IsSectionCorrection σ' h)
    (hk : σ'.r = σ.r + S.g ≫ k) :
    k = -h := sorry

end Splitting

namespace Hom

variable {S T : ShortComplex C}

/-- A morphism of split short complexes respects the chosen retractions and sections. -/
def RespectsSplittings (φ : S ⟶ T) (σ : S.Splitting) (τ : T.Splitting) : Prop :=
  φ.τ₂ ≫ τ.r = σ.r ≫ φ.τ₁ ∧ σ.s ≫ φ.τ₂ = φ.τ₃ ≫ τ.s

/-- Compatibility with splittings identifies the induced maps on the retract summands. -/
theorem RespectsSplittings.retraction {φ : S ⟶ T} {σ : S.Splitting} {τ : T.Splitting}
    (h : φ.RespectsSplittings σ τ) : φ.τ₂ ≫ τ.r = σ.r ≫ φ.τ₁ := sorry

/-- Compatibility with splittings identifies the induced maps on the section summands. -/
theorem RespectsSplittings.section {φ : S ⟶ T} {σ : S.Splitting} {τ : T.Splitting}
    (h : φ.RespectsSplittings σ τ) : σ.s ≫ φ.τ₂ = φ.τ₃ ≫ τ.s := sorry

/-- Identity morphisms respect every chosen splitting. -/
theorem respectsSplittings_id (σ : S.Splitting) :
    RespectsSplittings (𝟙 S) σ σ := sorry

/-- A composite respects splittings when both of its factors do. -/
theorem RespectsSplittings.comp {R : ShortComplex C} {φ : S ⟶ T} {ψ : T ⟶ R}
    {σ : S.Splitting} {τ : T.Splitting} {υ : R.Splitting}
    (hφ : φ.RespectsSplittings σ τ) (hψ : ψ.RespectsSplittings τ υ) :
    (φ ≫ ψ).RespectsSplittings σ υ := sorry

end Hom

namespace Hom

variable {S T : ShortComplex (HomologicalComplex C c)}

/-- A morphism of short complexes of homological complexes respects chosen splittings in every
degree. -/
def RespectsDegreewiseSplittings (φ : S ⟶ T)
    (σ : DegreewiseSplitting S) (τ : DegreewiseSplitting T) : Prop :=
  ∀ i, ((eval C c i).mapShortComplex.map φ).RespectsSplittings (σ i) (τ i)

/-- Degreewise compatibility specializes to compatibility in any fixed degree. -/
theorem RespectsDegreewiseSplittings.app {φ : S ⟶ T}
    {σ : DegreewiseSplitting S} {τ : DegreewiseSplitting T}
    (h : φ.RespectsDegreewiseSplittings σ τ) (i : ι) :
    ((eval C c i).mapShortComplex.map φ).RespectsSplittings (σ i) (τ i) := sorry

/-- Identity morphisms preserve every chosen degreewise splitting. -/
theorem respectsDegreewiseSplittings_id (σ : DegreewiseSplitting S) :
    RespectsDegreewiseSplittings (𝟙 S) σ σ := sorry

/-- A composite preserves degreewise splittings when both factors do. -/
theorem RespectsDegreewiseSplittings.comp
    {R : ShortComplex (HomologicalComplex C c)} {φ : S ⟶ T} {ψ : T ⟶ R}
    {σ : DegreewiseSplitting S} {τ : DegreewiseSplitting T}
    {υ : DegreewiseSplitting R} (hφ : φ.RespectsDegreewiseSplittings σ τ)
    (hψ : ψ.RespectsDegreewiseSplittings τ υ) :
    (φ ≫ ψ).RespectsDegreewiseSplittings σ υ := sorry

end Hom

namespace DegreewiseSplitting

variable {S T R : ShortComplex (HomologicalComplex C c)}

/-- Morphisms between two chosen degreewise splittings are short-complex morphisms compatible
with the retractions and sections in every degree. -/
@[stacks 01A3 "morphisms of degreewise split short complexes"]
abbrev Hom (σ : DegreewiseSplitting S) (τ : DegreewiseSplitting T) :=
  { φ : S ⟶ T // φ.RespectsDegreewiseSplittings σ τ }

namespace Hom

/-- The identity morphism of a chosen degreewise splitting. -/
@[stacks 01A3 "identity morphism of a degreewise splitting"]
def id (σ : DegreewiseSplitting S) : Hom σ σ :=
  ⟨𝟙 S, ShortComplex.Hom.respectsDegreewiseSplittings_id σ⟩

/-- Composition of morphisms preserving chosen degreewise splittings. -/
@[stacks 01A3 "composition of degreewise-splitting morphisms"]
def comp {σ : DegreewiseSplitting S} {τ : DegreewiseSplitting T}
    {υ : DegreewiseSplitting R} (φ : Hom σ τ) (ψ : Hom τ υ) : Hom σ υ :=
  ⟨φ.1 ≫ ψ.1, φ.2.comp ψ.2⟩

/-- The underlying short-complex morphism of the identity is the identity. -/
@[simp]
theorem id_val (σ : DegreewiseSplitting S) : (id σ).1 = 𝟙 S := sorry

/-- The underlying short-complex morphism of a composite is the composite of the underlying
morphisms. -/
@[simp]
theorem comp_val {σ : DegreewiseSplitting S} {τ : DegreewiseSplitting T}
    {υ : DegreewiseSplitting R} (φ : Hom σ τ) (ψ : Hom τ υ) :
    (comp φ ψ).1 = φ.1 ≫ ψ.1 := sorry

/-- Morphisms of chosen degreewise splittings are equal when their underlying short-complex
morphisms are equal. -/
@[ext]
theorem ext {σ : DegreewiseSplitting S} {τ : DegreewiseSplitting T}
    {φ ψ : Hom σ τ} (h : φ.1 = ψ.1) : φ = ψ := sorry

end Hom

end DegreewiseSplitting

end CategoryTheory.ShortComplex

namespace CochainComplex

noncomputable section

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace homOfDegreewiseSplit

/-- The unshifted coordinate of the degree-`n` connecting map associated to a degreewise
splitting of a short complex of cochain complexes. -/
@[stacks 011J "cochain degreewise connecting-map coordinate"]
def coordinate (S : ShortComplex (CochainComplex C ℤ))
    (σ : ShortComplex.DegreewiseSplitting S) (n : ℤ) :
    S.X₃.X n ⟶ S.X₁.X (n + 1) :=
  (σ n).s ≫ S.X₂.d n (n + 1) ≫ (σ (n + 1)).r

/-- The degree-`n` component of the connecting map associated to a degreewise splitting of a
short complex of cochain complexes. -/
@[stacks 011J "cochain degreewise connecting-map component"]
def component (S : ShortComplex (CochainComplex C ℤ))
    (σ : ShortComplex.DegreewiseSplitting S) (n : ℤ) :
    S.X₃.X n ⟶ (S.X₁⟦(1 : ℤ)⟧).X n :=
  coordinate S σ n ≫ (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).inv

/-- Transporting the shifted component back to its unshifted coordinate recovers
`coordinate`. -/
theorem component_comp_xIso (S : ShortComplex (CochainComplex C ℤ))
    (σ : ShortComplex.DegreewiseSplitting S) (n : ℤ) :
    component S σ n ≫ (S.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom =
      coordinate S σ n := sorry

/-- The raw connecting-map components commute with the cochain differentials. -/
theorem comm (S : ShortComplex (CochainComplex C ℤ))
    (σ : ShortComplex.DegreewiseSplitting S) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    component S σ i ≫ (S.X₁⟦(1 : ℤ)⟧).d i j =
      S.X₃.d i j ≫ component S σ j := sorry

/-- The canonical connecting map has the raw component exposed by `component`. -/
theorem component_eq (S : ShortComplex (CochainComplex C ℤ))
    (σ : ShortComplex.DegreewiseSplitting S) (n : ℤ) :
    (homOfDegreewiseSplit S σ).f n = component S σ n := sorry

end homOfDegreewiseSplit

end

end CochainComplex
