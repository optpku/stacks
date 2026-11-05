/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.FilteredInjective
public import ReasLib.Algebra.Homology.CochainComplex.Filtration.StrictReplacement
public import ReasLib.CategoryTheory.Filtration.Complex.Finite
public import ReasLib.CategoryTheory.Filtration.FiniteInjective.Embedding
public import ReasLib.CategoryTheory.Filtration.KernelCokernel
public import ReasLib.CategoryTheory.Filtration.FiniteBiproduct
public import ReasLib.Algebra.Homology.CochainComplex.Filtration.FilteredInjective.Horseshoe
public import ReasLib.CategoryTheory.Homology.DoubleComplex.TotalSupport
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Strict Filtered-Injective Resolutions

This leaf specializes the property-neutral strict replacement datum to finite filtered objects.
It owns both the replacement of a degree-zero complex and the compatible lifting of morphisms
between such replacements.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FilteredInjectivePlus

/-- A bounded-below, termwise monomorphic strict filtered-injective replacement whose associated
graded comparison is a quasi-isomorphism. -/
@[stacks 05TT "strict filtered-injective replacement"]
abbrev IsStrictReplacement
    (a : ℤ) {K : CochainComplex (FilteredObject.Finite.category C) ℤ}
    (I : FilteredInjectivePlus C)
    (f : K ⟶ (FilteredInjectivePlus.ι C).obj I) : Prop :=
  _root_.CochainComplex.FilteredReplacement.IsStrict
    (FilteredObject.Finite.inclusion C)
    (FilteredObject.Finite.AssociatedGraded.functor C)
    (FilteredObject.Finite.FilteredInjective.property C) a I f

/-- A chosen strict filtered-injective resolution of a bounded-below complex of finite filtered
objects.  The lower bound belongs to the chosen resolution; downstream constructions only need
the bundled bounded-below source. -/
@[stacks 05TW "strict filtered-injective resolution"]
structure Resolution (K : CochainComplex.Plus (FilteredObject.Finite.category C)) where
  /-- A lower bound respected by the chosen resolving complex. -/
  lowerBound : ℤ
  /-- The bounded-below termwise filtered-injective resolving complex. -/
  complex : FilteredInjectivePlus C
  /-- The comparison from the original complex to the resolving complex. -/
  ι : K.obj ⟶ (FilteredInjectivePlus.ι C).obj complex
  /-- The comparison is termwise monomorphic and strict, and is a filtered quasi-isomorphism. -/
  isStrict : IsStrictReplacement lowerBound complex ι

namespace Single

open FilteredObject.Finite.FilteredInjective

/-- The successive objects to be embedded: start with `A` and then take the quotient-filtered
cokernel of the preceding diagonal. The interval is fixed throughout this recursion, so no
finite-filtration or resolution existence theorem is used to choose the next object. -/
def cokernelStage [EnoughInjectives C] (A : FilteredObject C) (a b : ℤ) :
    ℕ → FilteredObject C
  | 0 => A
  | n + 1 => FilteredObject.Hom.cokernel
      (Embedding.inclusionAtBounds (cokernelStage A a b n) a b)

/-- Each resolving term is the explicit split injective target of the current cokernel. -/
def term [EnoughInjectives C] (A : FilteredObject C) (a b : ℤ) (n : ℕ) :
    FilteredObject.Finite.category C :=
  (Embedding.targetAtBounds (cokernelStage A a b n) a b).obj

/-- The next differential is the cokernel projection followed by the next diagonal embedding. -/
def differential [EnoughInjectives C] (A : FilteredObject C) (a b : ℤ) (n : ℕ) :
    term A a b n ⟶ term A a b (n + 1) :=
  ⟨FilteredObject.Hom.toCokernel
      (Embedding.inclusionAtBounds (cokernelStage A a b n) a b) ≫
    Embedding.inclusionAtBounds (cokernelStage A a b (n + 1)) a b⟩

/-- Consecutive differentials compose to zero by the ambient cokernel relation. -/
theorem differential_comp [EnoughInjectives C] (A : FilteredObject C) (a b : ℤ) (n : ℕ) :
    differential A a b n ≫ differential A a b (n + 1) = 0 := by
  apply ObjectProperty.hom_ext
  apply FilteredObject.Hom.ext
  change (cokernel.π (Embedding.diagonal (cokernelStage A a b n) a b) ≫
      Embedding.diagonal (cokernelStage A a b (n + 1)) a b) ≫
    (cokernel.π (Embedding.diagonal (cokernelStage A a b (n + 1)) a b) ≫
      Embedding.diagonal (cokernelStage A a b (n + 1 + 1)) a b) = 0
  erw [Category.assoc,
    ← Category.assoc (Embedding.diagonal (cokernelStage A a b (n + 1)) a b),
    cokernel.condition, zero_comp, comp_zero]

/-- The actual nonnegative complex of split filtered injectives in 05TT. -/
def natComplex [EnoughInjectives C] (A : FilteredObject C) (a b : ℤ) :
    CochainComplex (FilteredObject.Finite.category C) ℕ :=
  CochainComplex.of (term A a b) (differential A a b) (differential_comp A a b)

/-- Extend the nonnegative resolution by literal zero objects in negative degrees. -/
def complex [EnoughInjectives C] (A : FilteredObject C) (a b : ℤ) :
    CochainComplex (FilteredObject.Finite.category C) ℤ :=
  (natComplex A a b).extend ComplexShape.embeddingUpNat

/-- Extend a map of successive cokernels across the source diagonal, directly into the
original injective summands of the target. No injectivity certificate of a generated
resolution term is used to choose the extension. -/
def extendStageHom [EnoughInjectives C] (A B : FilteredObject C) (a b c d : ℤ)
    (n : ℕ) (g : (cokernelStage A a b n).obj ⟶ (cokernelStage B c d n).obj) :
    (term A a b n).obj.obj ⟶ (term B c d n).obj.obj :=
  FilteredObject.IntervalSplit.extendHom c d
    (fun i ↦ (Embedding.quotientPresentation (cokernelStage B c d n) c d i).J)
    (fun i ↦ (Embedding.quotientPresentation (cokernelStage B c d n) c d i).injective)
    (cokernelStage A a b n) (term A a b n).obj
    (g ≫ Embedding.diagonal (cokernelStage B c d n) c d)
    (Embedding.diagonal (cokernelStage A a b n) a b)

/-- The recursive cokernel comparisons. Each step descends the preceding extended map
followed by the target cokernel projection. Descent tests the zero-composite condition,
so no deferred commutation law supplies data to the recursion. -/
def stageMapHom [EnoughInjectives C] (A B : FilteredObject C) (a b c d : ℤ)
    (f : A.obj ⟶ B.obj) :
    (n : ℕ) → (cokernelStage A a b n).obj ⟶ (cokernelStage B c d n).obj
  | 0 => f
  | n + 1 => FilteredObject.Finite.FilteredInjective.cokernelDescOrZero
      (Embedding.diagonal (cokernelStage A a b n) a b)
      (extendStageHom A B a b c d n (stageMapHom A B a b c d f n) ≫
        cokernel.π (Embedding.diagonal (cokernelStage B c d n) c d))

/-- The actual component map between the two single-object resolutions. -/
def termMapHom [EnoughInjectives C] (A B : FilteredObject C) (a b c d : ℤ)
    (f : A.obj ⟶ B.obj) (n : ℕ) :
    (term A a b n).obj.obj ⟶ (term B c d n).obj.obj :=
  extendStageHom A B a b c d n (stageMapHom A B a b c d f n)

/-- The component formula preserves filtration. Only the source bounds are needed to
make the source diagonals strict monomorphisms. -/
theorem termMapHom_preserves [EnoughInjectives C] {A B : FilteredObject C}
    (f : A ⟶ B) (a b c d : ℤ) (hab : a ≤ b)
    (ha : A.filtration.stage a = ⊤) (hb : A.filtration.stage (b + 1) = ⊥)
    (n : ℕ) (p : ℤ) :
    ((term B c d n).obj.filtration.stage p).Factors
      (((term A a b n).obj.filtration.stage p).arrow ≫
        termMapHom A B a b c d f.hom n) := sorry

/-- Bundle the explicit component as a map of finite filtered objects. -/
def termMap [EnoughInjectives C] {A B : FilteredObject C}
    (f : A ⟶ B) (a b c d : ℤ) (hab : a ≤ b)
    (ha : A.filtration.stage a = ⊤) (hb : A.filtration.stage (b + 1) = ⊥)
    (n : ℕ) : term A a b n ⟶ term B c d n :=
  ⟨FilteredObject.Hom.mk (termMapHom A B a b c d f.hom n)
    (termMapHom_preserves f a b c d hab ha hb n)⟩

/-- The component comparisons commute with the cokernel differentials. -/
theorem termMap_comm [EnoughInjectives C] {A B : FilteredObject C}
    (f : A ⟶ B) (a b c d : ℤ) (hab : a ≤ b)
    (ha : A.filtration.stage a = ⊤) (hb : A.filtration.stage (b + 1) = ⊥) (n : ℕ) :
    termMap f a b c d hab ha hb n ≫ (natComplex B c d).d n (n + 1) =
      (natComplex A a b).d n (n + 1) ≫ termMap f a b c d hab ha hb (n + 1) := sorry

/-- The comparison of nonnegative resolutions constructed by successive extension and
cokernel descent, as in 05TU. -/
def natMap [EnoughInjectives C] {A B : FilteredObject C}
    (f : A ⟶ B) (a b c d : ℤ) (hab : a ≤ b)
    (ha : A.filtration.stage a = ⊤) (hb : A.filtration.stage (b + 1) = ⊥) :
    natComplex A a b ⟶ natComplex B c d :=
  CochainComplex.ofHom (termMap f a b c d hab ha hb)
    (termMap_comm f a b c d hab ha hb)

/-- The single-resolution comparison, extended by zero to negative degrees. -/
def map [EnoughInjectives C] {A B : FilteredObject C}
    (f : A ⟶ B) (a b c d : ℤ) (hab : a ≤ b)
    (ha : A.filtration.stage a = ⊤) (hb : A.filtration.stage (b + 1) = ⊥) :
    complex A a b ⟶ complex B c d :=
  HomologicalComplex.extendMap (natMap f a b c d hab ha hb) ComplexShape.embeddingUpNat

/-- The complex is zero in negative degrees by the extension construction. -/
theorem strictlyGE [EnoughInjectives C] (A : FilteredObject C) (a b : ℤ) :
    (complex A a b).IsStrictlyGE 0 := by
  dsimp [complex]
  infer_instance

/-- Every term is filtered injective: nonnegative terms are the split targets, and negative
terms are the zero object. This certificate is never used to select resolution data. -/
theorem term_filteredInjective [EnoughInjectives C] (A : FilteredObject C) (a b n : ℤ) :
    FilteredObject.Finite.FilteredInjective.property C ((complex A a b).X n) := sorry

/-- Package the explicitly constructed complex with its boundedness and injectivity laws. -/
def bundled [EnoughInjectives C] (A : FilteredObject C) (a b : ℤ) :
    FilteredInjectivePlus C :=
  ⟨⟨complex A a b, ⟨0, strictlyGE A a b⟩⟩, term_filteredInjective A a b⟩

/-- The augmentation is the first diagonal, transported through the standard degree-zero
identification for extension from `ℕ` to `ℤ`. -/
def augmentation [EnoughInjectives C] (A : FilteredObject.Finite.category C) (a b : ℤ) :
    A ⟶ (complex A.obj a b).X 0 :=
  (⟨Embedding.inclusionAtBounds A.obj a b⟩ : A ⟶ term A.obj a b 0) ≫
    ((natComplex A.obj a b).extendXIso ComplexShape.embeddingUpNat rfl).inv

/-- The augmentation is killed by the first differential. -/
theorem augmentation_comp_d [EnoughInjectives C]
    (A : FilteredObject.Finite.category C) (a b : ℤ) (n : ℤ)
    (hn : (ComplexShape.up ℤ).Rel 0 n) :
    augmentation A a b ≫ (complex A.obj a b).d 0 n = 0 := sorry

/-- The map from `A[0]`, with the displayed augmentation in degree zero and zero components
elsewhere. In particular, it is not chosen from the single-object existence theorem. -/
def comparison [EnoughInjectives C] (A : FilteredObject.Finite.category C) (a b : ℤ) :
    (CochainComplex.singleFunctor (FilteredObject.Finite.category C) (0 : ℤ)).obj A ⟶
      (FilteredInjectivePlus.ι C).obj (bundled A.obj a b) :=
  HomologicalComplex.mkHomFromSingle (augmentation A a b) (augmentation_comp_d A a b)

/-- The constructed single-resolution map lifts the original filtered morphism. -/
theorem comparison_naturality [EnoughInjectives C]
    {A B : FilteredObject.Finite.category C} (f : A ⟶ B) (a b c d : ℤ)
    (hab : a ≤ b) (ha : A.obj.filtration.stage a = ⊤)
    (hb : A.obj.filtration.stage (b + 1) = ⊥) :
    comparison A a b ≫ map f.hom a b c d hab ha hb =
      (CochainComplex.singleFunctor (FilteredObject.Finite.category C) (0 : ℤ)).map f ≫
        comparison B c d := sorry

/-- The same filtration bounds work for every successive quotient. They are retained as
explicit parameters rather than chosen again from a deferred finiteness theorem. -/
theorem cokernelStage_bounds [EnoughInjectives C] (A : FilteredObject C) (a b : ℤ)
    (ha : A.filtration.stage a = ⊤) (hb : A.filtration.stage (b + 1) = ⊥) (n : ℕ) :
    (cokernelStage A a b n).filtration.stage a = ⊤ ∧
      (cokernelStage A a b n).filtration.stage (b + 1) = ⊥ := sorry

/-- The iterated strict embeddings and cokernel sequences give the strict replacement law of
05TT. The law is separate from every object, differential, and comparison definition. -/
theorem isStrictReplacement [EnoughInjectives C]
    (A : FilteredObject.Finite.category C) (a b : ℤ) (hab : a ≤ b)
    (ha : A.obj.filtration.stage a = ⊤) (hb : A.obj.filtration.stage (b + 1) = ⊥) :
    IsStrictReplacement 0 (bundled A.obj a b) (comparison A a b) := sorry

/-- The degree-zero source as a bounded-below complex. -/
def source (A : FilteredObject.Finite.category C) :
    CochainComplex.Plus (FilteredObject.Finite.category C) :=
  ⟨(CochainComplex.singleFunctor (FilteredObject.Finite.category C) (0 : ℤ)).obj A,
    ⟨0, inferInstance⟩⟩

end Single

namespace SingleHorseshoe

open FilteredObject.Finite.FilteredInjective
attribute [local instance] Abelian.hasFiniteBiproducts

variable [EnoughInjectives C]

/-- The source conditions for the explicit horseshoe: graded short exactness and the
original filtration bounds of the two outer objects. -/
def Valid (S : ShortComplex (FilteredObject.Finite.category C)) (a b c d : ℤ) : Prop :=
  (S.map (FilteredObject.Finite.AssociatedGraded.functor C)).ShortExact ∧
    a ≤ b ∧ c ≤ d ∧ S.X₁.obj.filtration.stage a = ⊤ ∧
    S.X₁.obj.filtration.stage (b + 1) = ⊥ ∧ S.X₃.obj.filtration.stage c = ⊤ ∧
    S.X₃.obj.filtration.stage (d + 1) = ⊥

/-- The middle resolving term is the existing stagewise biproduct model. -/
def term (S : ShortComplex (FilteredObject.Finite.category C)) (a b c d : ℤ) (n : ℕ) :
    FilteredObject.Finite.category C :=
  ⟨FilteredObject.binaryBiproduct (Single.term S.X₁.obj a b n).obj
      (Single.term S.X₃.obj c d n).obj,
    FilteredObject.IsFinite.binaryBiproduct (Single.term S.X₁.obj a b n).property
      (Single.term S.X₃.obj c d n).property⟩

/-- One actual quotient stage in the horseshoe recursion. No law certificate supplies
any of its data; the two maps are ambient maps, with their laws proved separately. -/
structure Stage (S : ShortComplex (FilteredObject.Finite.category C))
    (a b c d : ℤ) (n : ℕ) where
  middle : FilteredObject C
  left : (Single.cokernelStage S.X₁.obj a b n).obj ⟶ middle.obj
  right : middle.obj ⟶ (Single.cokernelStage S.X₃.obj c d n).obj

/-- Extend the left diagonal into its original summands and pair it with the right diagonal. -/
def Stage.embeddingHom {S : ShortComplex (FilteredObject.Finite.category C)}
    {a b c d : ℤ} {n : ℕ} (T : Stage S a b c d n) :
    T.middle.obj ⟶ (term S a b c d n).obj.obj :=
  biprod.lift
    (FilteredObject.IntervalSplit.extendHom a b
      (fun i ↦ (Embedding.quotientPresentation (Single.cokernelStage S.X₁.obj a b n) a b i).J)
      (fun i ↦ (Embedding.quotientPresentation (Single.cokernelStage S.X₁.obj a b n) a b i).injective)
      (Single.cokernelStage S.X₁.obj a b n) T.middle
      (Embedding.diagonal (Single.cokernelStage S.X₁.obj a b n) a b) T.left)
    (T.right ≫ Embedding.diagonal (Single.cokernelStage S.X₃.obj c d n) c d)

/-- Pass to the three cokernels, using total cokernel descent for their comparison maps. -/
def Stage.next {S : ShortComplex (FilteredObject.Finite.category C)}
    {a b c d : ℤ} {n : ℕ} (T : Stage S a b c d n) : Stage S a b c d (n + 1) where
  middle := (term S a b c d n).obj.pushforward (cokernel.π T.embeddingHom)
  left := cokernelDescOrZero (Embedding.diagonal (Single.cokernelStage S.X₁.obj a b n) a b)
    (biprod.inl ≫ cokernel.π T.embeddingHom)
  right := cokernelDescOrZero T.embeddingHom
    (biprod.snd ≫ cokernel.π (Embedding.diagonal (Single.cokernelStage S.X₃.obj c d n) c d))

/-- The complete explicit recursion starts from the given short complex. -/
def stage (S : ShortComplex (FilteredObject.Finite.category C)) (a b c d : ℤ) :
    (n : ℕ) → Stage S a b c d n
  | 0 => ⟨S.X₂.obj, S.f.hom.hom, S.g.hom.hom⟩
  | n + 1 => (stage S a b c d n).next

/-- The ambient differential factors through the actual middle cokernel. -/
def differentialHom (S : ShortComplex (FilteredObject.Finite.category C))
    (a b c d : ℤ) (n : ℕ) :
    (term S a b c d n).obj.obj ⟶ (term S a b c d (n + 1)).obj.obj :=
  cokernel.π (stage S a b c d n).embeddingHom ≫ (stage S a b c d (n + 1)).embeddingHom

theorem differentialHom_preserves (S : ShortComplex (FilteredObject.Finite.category C))
    (a b c d : ℤ) (h : Valid S a b c d) (n : ℕ) (p : ℤ) :
    ((term S a b c d (n + 1)).obj.filtration.stage p).Factors
      (((term S a b c d n).obj.filtration.stage p).arrow ≫
        differentialHom S a b c d n) := sorry

/-- The filtered middle differential, with only its filtration law deferred. -/
def differential (S : ShortComplex (FilteredObject.Finite.category C))
    (a b c d : ℤ) (h : Valid S a b c d) (n : ℕ) :
    term S a b c d n ⟶ term S a b c d (n + 1) :=
  ⟨FilteredObject.Hom.mk (differentialHom S a b c d n)
    (differentialHom_preserves S a b c d h n)⟩

theorem differential_comp (S : ShortComplex (FilteredObject.Finite.category C))
    (a b c d : ℤ) (h : Valid S a b c d) (n : ℕ) :
    differential S a b c d h n ≫ differential S a b c d h (n + 1) = 0 := by
  apply ObjectProperty.hom_ext
  apply FilteredObject.Hom.ext
  change (cokernel.π _ ≫ _) ≫ (cokernel.π _ ≫ _) = 0
  erw [Category.assoc, ← Category.assoc (stage S a b c d (n + 1)).embeddingHom,
    cokernel.condition, zero_comp, comp_zero]

/-- The nonnegative middle complex of the horseshoe. -/
def natComplex (S : ShortComplex (FilteredObject.Finite.category C))
    (a b c d : ℤ) (h : Valid S a b c d) :
    CochainComplex (FilteredObject.Finite.category C) ℕ :=
  CochainComplex.of (term S a b c d) (differential S a b c d h)
    (differential_comp S a b c d h)

/-- The middle complex, extended by zero below degree zero. -/
def complex (S : ShortComplex (FilteredObject.Finite.category C))
    (a b c d : ℤ) (h : Valid S a b c d) :
    CochainComplex (FilteredObject.Finite.category C) ℤ :=
  (natComplex S a b c d h).extend ComplexShape.embeddingUpNat

/-- The canonical degreewise inclusion, with its explicit ambient biproduct formula. -/
def leftTerm (S : ShortComplex (FilteredObject.Finite.category C)) (a b c d : ℤ) (n : ℕ) :
    Single.term S.X₁.obj a b n ⟶ term S a b c d n :=
  ⟨FilteredObject.Hom.mk biprod.inl (by
    intro p
    change (Subobject.mk (DecreasingFiltration.biprodMap _ _ p)).Factors _
    rw [Subobject.mk_factors_iff]
    exact ⟨biprod.inl, by simp [DecreasingFiltration.biprodMap] <;> rfl⟩)⟩

/-- The canonical degreewise projection. -/
def rightTerm (S : ShortComplex (FilteredObject.Finite.category C)) (a b c d : ℤ) (n : ℕ) :
    term S a b c d n ⟶ Single.term S.X₃.obj c d n :=
  ⟨(FilteredObject.Finite.binaryBiproductFan
    (Single.term S.X₁.obj a b n).obj (Single.term S.X₃.obj c d n).obj).snd⟩

theorem leftTerm_comm (S : ShortComplex (FilteredObject.Finite.category C))
    (a b c d : ℤ) (h : Valid S a b c d) (n : ℕ) :
    leftTerm S a b c d n ≫ (natComplex S a b c d h).d n (n + 1) =
      (Single.natComplex S.X₁.obj a b).d n (n + 1) ≫ leftTerm S a b c d (n + 1) := sorry

theorem rightTerm_comm (S : ShortComplex (FilteredObject.Finite.category C))
    (a b c d : ℤ) (h : Valid S a b c d) (n : ℕ) :
    rightTerm S a b c d n ≫ (Single.natComplex S.X₃.obj c d).d n (n + 1) =
      (natComplex S a b c d h).d n (n + 1) ≫ rightTerm S a b c d (n + 1) := sorry

/-- The left chain map is the extension by zero of the explicit inclusions. -/
def left (S : ShortComplex (FilteredObject.Finite.category C))
    (a b c d : ℤ) (h : Valid S a b c d) :
    Single.complex S.X₁.obj a b ⟶ complex S a b c d h :=
  HomologicalComplex.extendMap
    (CochainComplex.ofHom (leftTerm S a b c d) (leftTerm_comm S a b c d h))
    ComplexShape.embeddingUpNat

/-- The right chain map is the extension by zero of the explicit projections. -/
def right (S : ShortComplex (FilteredObject.Finite.category C))
    (a b c d : ℤ) (h : Valid S a b c d) :
    complex S a b c d h ⟶ Single.complex S.X₃.obj c d :=
  HomologicalComplex.extendMap
    (CochainComplex.ofHom (rightTerm S a b c d) (rightTerm_comm S a b c d h))
    ComplexShape.embeddingUpNat

theorem left_right (S : ShortComplex (FilteredObject.Finite.category C))
    (a b c d : ℤ) (h : Valid S a b c d) : left S a b c d h ≫ right S a b c d h = 0 := sorry

theorem embedding_preserves (S : ShortComplex (FilteredObject.Finite.category C))
    (a b c d : ℤ) (h : Valid S a b c d) (p : ℤ) :
    ((term S a b c d 0).obj.filtration.stage p).Factors
      ((S.X₂.obj.filtration.stage p).arrow ≫ (stage S a b c d 0).embeddingHom) := sorry

/-- The actual middle augmentation in degree zero. -/
def augmentation (S : ShortComplex (FilteredObject.Finite.category C))
    (a b c d : ℤ) (h : Valid S a b c d) : S.X₂ ⟶ (complex S a b c d h).X 0 :=
  (⟨FilteredObject.Hom.mk (stage S a b c d 0).embeddingHom
    (embedding_preserves S a b c d h)⟩ : S.X₂ ⟶ term S a b c d 0) ≫
    ((natComplex S a b c d h).extendXIso ComplexShape.embeddingUpNat rfl).inv

theorem augmentation_comp_d (S : ShortComplex (FilteredObject.Finite.category C))
    (a b c d : ℤ) (h : Valid S a b c d) (n : ℤ) (hn : (ComplexShape.up ℤ).Rel 0 n) :
    augmentation S a b c d h ≫ (complex S a b c d h).d 0 n = 0 := sorry

/-- The middle comparison from the original object concentrated in degree zero. -/
def comparison (S : ShortComplex (FilteredObject.Finite.category C))
    (a b c d : ℤ) (h : Valid S a b c d) :
    (CochainComplex.singleFunctor (FilteredObject.Finite.category C) (0 : ℤ)).obj S.X₂ ⟶
      complex S a b c d h :=
  HomologicalComplex.mkHomFromSingle (augmentation S a b c d h) (augmentation_comp_d S a b c d h)

/-- The termwise retraction is the actual first projection of the stagewise biproduct. -/
def retractionTerm (S : ShortComplex (FilteredObject.Finite.category C)) (a b c d : ℤ) (n : ℕ) :
    term S a b c d n ⟶ Single.term S.X₁.obj a b n :=
  ⟨(FilteredObject.Finite.binaryBiproductFan
    (Single.term S.X₁.obj a b n).obj (Single.term S.X₃.obj c d n).obj).fst⟩

/-- The termwise section is the second biproduct inclusion. -/
def sectionTerm (S : ShortComplex (FilteredObject.Finite.category C)) (a b c d : ℤ) (n : ℕ) :
    Single.term S.X₃.obj c d n ⟶ term S a b c d n :=
  ⟨FilteredObject.Hom.mk biprod.inr (by
    intro p
    change (Subobject.mk (DecreasingFiltration.biprodMap _ _ p)).Factors _
    rw [Subobject.mk_factors_iff]
    exact ⟨biprod.inr, by simp [DecreasingFiltration.biprodMap] <;> rfl⟩)⟩

/-- Transport the actual projection in nonnegative degrees and use zero below zero. -/
def retraction (S : ShortComplex (FilteredObject.Finite.category C))
    (a b c d : ℤ) (h : Valid S a b c d) (p : ℤ) :
    (complex S a b c d h).X p ⟶ (Single.complex S.X₁.obj a b).X p := by
  classical
  exact if hp : 0 ≤ p then
    let hn : (ComplexShape.embeddingUpNat).f p.toNat = p := by simpa using Int.toNat_of_nonneg hp
    ((natComplex S a b c d h).extendXIso ComplexShape.embeddingUpNat hn).hom ≫
      retractionTerm S a b c d p.toNat ≫
      ((Single.natComplex S.X₁.obj a b).extendXIso ComplexShape.embeddingUpNat hn).inv
  else 0

/-- Transport the actual inclusion in nonnegative degrees and use zero below zero. -/
def sectionMap (S : ShortComplex (FilteredObject.Finite.category C))
    (a b c d : ℤ) (h : Valid S a b c d) (p : ℤ) :
    (Single.complex S.X₃.obj c d).X p ⟶ (complex S a b c d h).X p := by
  classical
  exact if hp : 0 ≤ p then
    let hn : (ComplexShape.embeddingUpNat).f p.toNat = p := by simpa using Int.toNat_of_nonneg hp
    ((Single.natComplex S.X₃.obj c d).extendXIso ComplexShape.embeddingUpNat hn).hom ≫
      sectionTerm S a b c d p.toNat ≫
      ((natComplex S a b c d h).extendXIso ComplexShape.embeddingUpNat hn).inv
  else 0

theorem term_filteredInjective (S : ShortComplex (FilteredObject.Finite.category C))
    (a b c d : ℤ) (h : Valid S a b c d) (p : ℤ) :
    FilteredObject.Finite.FilteredInjective.property C ((complex S a b c d h).X p) := sorry

/-- Bundle the concrete middle complex; none of its law certificates is used for extension. -/
def bundled (S : ShortComplex (FilteredObject.Finite.category C))
    (a b c d : ℤ) (h : Valid S a b c d) : FilteredInjectivePlus C :=
  ⟨⟨complex S a b c d h, ⟨0, by dsimp only [complex]; infer_instance⟩⟩,
    term_filteredInjective S a b c d h⟩

/-- The concrete horseshoe, with explicit maps, degreewise splitting, and comparison. -/
def horseshoe (S : ShortComplex (FilteredObject.Finite.category C))
    (a b c d : ℤ) (h : Valid S a b c d) :
    Horseshoe S (Single.comparison S.X₁ a b) (Single.comparison S.X₃ c d) where
  middle := bundled S a b c d h
  strictlyGE := by
    change (complex S a b c d h).IsStrictlyGE 0
    dsimp only [complex]
    infer_instance
  i := ⟨⟨left S a b c d h⟩⟩
  p := ⟨⟨right S a b c d h⟩⟩
  zero := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact left_right S a b c d h
  comparison :=
    { τ₁ := Single.comparison S.X₁ a b
      τ₂ := comparison S a b c d h
      τ₃ := Single.comparison S.X₃ c d
      comm₁₂ := by sorry
      comm₂₃ := by sorry }
  splitting p :=
    { r := retraction S a b c d h p
      s := sectionMap S a b c d h p
      f_r := by sorry
      s_g := by sorry
      id := by sorry }
  comparison_left := rfl
  comparison_right := rfl

end SingleHorseshoe

namespace BoundedConstruction

open FilteredObject.Finite.FilteredInjective
attribute [local instance] Abelian.hasFiniteBiproducts

variable [EnoughInjectives C]

/-- Only the supplied source boundedness chooses this integer. -/
def lowerBound (K : CochainComplex.Plus (FilteredObject.Finite.category C)) : ℤ :=
  K.property.choose

/-- The original term in the nonnegative indexing of the construction. -/
def sourceTerm (K : CochainComplex.Plus (FilteredObject.Finite.category C)) (n : ℕ) :=
  K.obj.X (lowerBound K + n)

/-- Bounds are chosen from the original finite filtered term, never from a generated law. -/
def lower (K : CochainComplex.Plus (FilteredObject.Finite.category C)) (n : ℕ) : ℤ :=
  Embedding.lowerBound (sourceTerm K n)

def upper (K : CochainComplex.Plus (FilteredObject.Finite.category C)) (n : ℕ) : ℤ :=
  Embedding.upperBound (sourceTerm K n)

def sourceDifferential (K : CochainComplex.Plus (FilteredObject.Finite.category C)) (n : ℕ) :
    sourceTerm K n ⟶ sourceTerm K (n + 1) :=
  K.obj.d (lowerBound K + n) (lowerBound K + (n + 1 : ℕ))

/-- The actual induced kernel. -/
def kernelObject (K : CochainComplex.Plus (FilteredObject.Finite.category C)) (n : ℕ) :
    FilteredObject C := FilteredObject.Hom.kernel (sourceDifferential K n).hom

/-- The actual quotient-filtered coimage. -/
def coimageObject (K : CochainComplex.Plus (FilteredObject.Finite.category C)) (n : ℕ) :
    FilteredObject C :=
  FilteredObject.Hom.cokernel (FilteredObject.Hom.kernelι (sourceDifferential K n).hom)

theorem kernel_bounds (K : CochainComplex.Plus (FilteredObject.Finite.category C)) (n : ℕ) :
    (kernelObject K n).filtration.stage (lower K n) = ⊤ ∧
      (kernelObject K n).filtration.stage (upper K n + 1) = ⊥ := sorry

theorem coimage_bounds (K : CochainComplex.Plus (FilteredObject.Finite.category C)) (n : ℕ) :
    (coimageObject K n).filtration.stage (lower K n) = ⊤ ∧
      (coimageObject K n).filtration.stage (upper K n + 1) = ⊥ := sorry

/-- Bundle finiteness without extracting any new bounds from that certificate. -/
def kernelTerm (K : CochainComplex.Plus (FilteredObject.Finite.category C)) (n : ℕ) :
    FilteredObject.Finite.category C :=
  ⟨kernelObject K n, ⟨lower K n, upper K n + 1, kernel_bounds K n⟩⟩

def coimageTerm (K : CochainComplex.Plus (FilteredObject.Finite.category C)) (n : ℕ) :
    FilteredObject.Finite.category C :=
  ⟨coimageObject K n, ⟨lower K n, upper K n + 1, coimage_bounds K n⟩⟩

/-- The canonical kernel/coimage short complex of the original differential. -/
def shortComplex (K : CochainComplex.Plus (FilteredObject.Finite.category C)) (n : ℕ) :
    ShortComplex (FilteredObject.Finite.category C) :=
  ShortComplex.mk
    (⟨FilteredObject.Hom.kernelι (sourceDifferential K n).hom⟩ : kernelTerm K n ⟶ sourceTerm K n)
    (⟨FilteredObject.Hom.toCokernel
      (FilteredObject.Hom.kernelι (sourceDifferential K n).hom)⟩ : sourceTerm K n ⟶ coimageTerm K n)
    (by
      apply ObjectProperty.hom_ext
      apply FilteredObject.Hom.ext
      exact cokernel.condition _)

theorem valid (K : CochainComplex.Plus (FilteredObject.Finite.category C)) (n : ℕ) :
    SingleHorseshoe.Valid (shortComplex K n) (lower K n) (upper K n)
      (lower K n) (upper K n) := sorry

/-- Factor the original differential through the next ambient kernel, then descend through
its source kernel. Both universal maps use genuine ambient kernel/cokernel data. -/
def connectingHom (K : CochainComplex.Plus (FilteredObject.Finite.category C)) (n : ℕ) :
    (coimageObject K n).obj ⟶ (kernelObject K (n + 1)).obj :=
  cokernelDescOrZero (kernelSubobject (sourceDifferential K n).hom.hom).arrow
    (kernel.lift (sourceDifferential K (n + 1)).hom.hom
      (sourceDifferential K n).hom.hom (by
        exact congrArg (fun f ↦ f.hom.hom)
          (K.obj.d_comp_d (lowerBound K + n) (lowerBound K + (n + 1 : ℕ))
            (lowerBound K + (n + 1 + 1 : ℕ)))) ≫
      (kernelSubobjectIso (sourceDifferential K (n + 1)).hom.hom).inv)

theorem connectingHom_preserves
    (K : CochainComplex.Plus (FilteredObject.Finite.category C)) (n : ℕ) (p : ℤ) :
    ((kernelObject K (n + 1)).filtration.stage p).Factors
      (((coimageObject K n).filtration.stage p).arrow ≫ connectingHom K n) := sorry

/-- The filtered coimage-to-next-kernel map from the source differential. -/
def connecting (K : CochainComplex.Plus (FilteredObject.Finite.category C)) (n : ℕ) :
    coimageTerm K n ⟶ kernelTerm K (n + 1) :=
  ⟨FilteredObject.Hom.mk (connectingHom K n) (connectingHom_preserves K n)⟩

/-- Lift the coimage-to-kernel map using the recursive single-resolution comparison. -/
def connectingMap (K : CochainComplex.Plus (FilteredObject.Finite.category C)) (n : ℕ) :
    Single.complex (coimageObject K n) (lower K n) (upper K n) ⟶
      Single.complex (kernelObject K (n + 1)) (lower K (n + 1)) (upper K (n + 1)) :=
  Single.map (connecting K n).hom (lower K n) (upper K n)
    (lower K (n + 1)) (upper K (n + 1))
    (Embedding.lowerBound_le_upperBound (sourceTerm K n))
    (coimage_bounds K n).1 (coimage_bounds K n).2

/-- The middle horseshoe resolving one original term. -/
def row (K : CochainComplex.Plus (FilteredObject.Finite.category C)) (n : ℕ) :=
  SingleHorseshoe.complex (shortComplex K n) (lower K n) (upper K n)
    (lower K n) (upper K n) (valid K n)

/-- The outer differential is beta, the lifted connecting map, then alpha. -/
def outerDifferential (K : CochainComplex.Plus (FilteredObject.Finite.category C)) (n : ℕ) :
    row K n ⟶ row K (n + 1) :=
  SingleHorseshoe.right (shortComplex K n) _ _ _ _ (valid K n) ≫ connectingMap K n ≫
    SingleHorseshoe.left (shortComplex K (n + 1)) _ _ _ _ (valid K (n + 1))

private theorem triple_composite_zero {D : Type*} [Category* D] [HasZeroMorphisms D]
    {A₁ A₂ A₃ A₄ A₅ A₆ A₇ : D} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃)
    (h : A₃ ⟶ A₄) (i : A₄ ⟶ A₅) (j : A₅ ⟶ A₆) (k : A₆ ⟶ A₇)
    (hi : h ≫ i = 0) : (f ≫ g ≫ h) ≫ (i ≫ j ≫ k) = 0 := by
  calc
    _ = f ≫ g ≫ (h ≫ i) ≫ j ≫ k := by simp only [Category.assoc]
    _ = 0 := by rw [hi, zero_comp, comp_zero, comp_zero]

theorem outerDifferential_comp (K : CochainComplex.Plus (FilteredObject.Finite.category C))
    (n : ℕ) : outerDifferential K n ≫ outerDifferential K (n + 1) = 0 :=
  triple_composite_zero
    (SingleHorseshoe.right (shortComplex K n) _ _ _ _ (valid K n)) (connectingMap K n)
    (SingleHorseshoe.left (shortComplex K (n + 1)) _ _ _ _ (valid K (n + 1)))
    (SingleHorseshoe.right (shortComplex K (n + 1)) _ _ _ _ (valid K (n + 1)))
    (connectingMap K (n + 1))
    (SingleHorseshoe.left (shortComplex K (n + 1 + 1)) _ _ _ _ (valid K (n + 1 + 1)))
    (SingleHorseshoe.left_right (shortComplex K (n + 1)) _ _ _ _ (valid K (n + 1)))

/-- The actual nonnegative complex of resolving complexes. -/
def outerNat (K : CochainComplex.Plus (FilteredObject.Finite.category C)) :
    CochainComplex (CochainComplex (FilteredObject.Finite.category C) ℤ) ℕ :=
  CochainComplex.of (row K) (outerDifferential K) (outerDifferential_comp K)

/-- Extend the outer direction by zero below the original source bound. -/
def doubleComplex (K : CochainComplex.Plus (FilteredObject.Finite.category C)) :
    HomologicalComplex₂ (FilteredObject.Finite.category C) (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (outerNat K).extend (ComplexShape.embeddingUpIntGE (lowerBound K))

/-- The support certificate is proved from the extension construction, not admitted. -/
theorem outer_strictlyGE (K : CochainComplex.Plus (FilteredObject.Finite.category C)) :
    CochainComplex.IsStrictlyGE (doubleComplex K) (lowerBound K) := by
  dsimp only [doubleComplex]
  infer_instance

theorem inner_strictlyGE (K : CochainComplex.Plus (FilteredObject.Finite.category C)) (p : ℤ) :
    CochainComplex.IsStrictlyGE ((doubleComplex K).X p) 0 := by
  classical
  let e := ComplexShape.embeddingUpIntGE (lowerBound K)
  by_cases hp : ∃ n, e.f n = p
  · obtain ⟨n, hn⟩ := hp
    letI : ((outerNat K).X n).IsStrictlyGE 0 := by
      change (row K n).IsStrictlyGE 0
      dsimp only [row, SingleHorseshoe.complex]
      infer_instance
    exact CochainComplex.isStrictlyGE_of_iso
      ((outerNat K).extendXIso e hn).symm 0
  · refine ⟨fun q hq ↦ ?_⟩
    exact (HomologicalComplex.eval (FilteredObject.Finite.category C) (ComplexShape.up ℤ) q).map_isZero
      ((outerNat K).isZero_extend_X e p (by simpa only [not_exists] using hp))

/-- Finite coproducts use the existing canonical finite filtered biproduct/zero owners. -/
local instance finiteCoproducts : HasFiniteCoproducts (FilteredObject.Finite.category C) := by
  exact hasFiniteCoproducts_of_has_binary_and_initial

/-- Only the proved pair of support bounds supplies the totalization data. -/
local instance hasTotal (K : CochainComplex.Plus (FilteredObject.Finite.category C)) :
    (doubleComplex K).HasTotal (ComplexShape.up ℤ) :=
  HomologicalComplex₂.AntidiagonalSupport.Finite.hasTotal_of_isStrictlyGE
    (outer_strictlyGE K) (inner_strictlyGE K)

/-- The coproduct total of the explicit commutative double complex in 05TW. -/
def total (K : CochainComplex.Plus (FilteredObject.Finite.category C)) :
    CochainComplex (FilteredObject.Finite.category C) ℤ :=
  (doubleComplex K).total (ComplexShape.up ℤ)

/-- In supported degrees, use the horseshoe augmentation followed by the total injection;
in degrees below the source bound, use the zero morphism. -/
def comparisonComponent (K : CochainComplex.Plus (FilteredObject.Finite.category C)) (p : ℤ) :
    K.obj.X p ⟶ (total K).X p := by
  classical
  exact if hp : lowerBound K ≤ p then
    let n := (p - lowerBound K).toNat
    let hn : lowerBound K + (n : ℤ) = p := by dsimp only [n]; omega
    (HomologicalComplex.XIsoOfEq K.obj hn.symm).hom ≫
      SingleHorseshoe.augmentation (shortComplex K n) _ _ _ _ (valid K n) ≫
      (((HomologicalComplex.eval (FilteredObject.Finite.category C) (ComplexShape.up ℤ) 0).mapIso
        ((outerNat K).extendXIso (ComplexShape.embeddingUpIntGE (lowerBound K)) hn)).inv) ≫
      (doubleComplex K).ιTotal (ComplexShape.up ℤ) p 0 p (by change p + 0 = p; omega)
  else 0

theorem comparisonComponent_comm
    (K : CochainComplex.Plus (FilteredObject.Finite.category C)) (p q : ℤ) :
    comparisonComponent K p ≫ (total K).d p q = K.obj.d p q ≫ comparisonComponent K q := sorry

/-- The actual augmentation to the total complex. -/
def comparison (K : CochainComplex.Plus (FilteredObject.Finite.category C)) : K.obj ⟶ total K where
  f := comparisonComponent K
  comm' := fun p q _ ↦ comparisonComponent_comm K p q

theorem total_strictlyGE (K : CochainComplex.Plus (FilteredObject.Finite.category C)) :
    (total K).IsStrictlyGE (lowerBound K) := sorry

theorem total_filteredInjective (K : CochainComplex.Plus (FilteredObject.Finite.category C))
    (p : ℤ) : FilteredObject.Finite.FilteredInjective.property C ((total K).X p) := sorry

/-- Bundle the actual total; its law certificates supply no subsequent data. -/
def bundled (K : CochainComplex.Plus (FilteredObject.Finite.category C)) : FilteredInjectivePlus C :=
  ⟨⟨total K, ⟨lowerBound K, total_strictlyGE K⟩⟩, total_filteredInjective K⟩

theorem isStrictReplacement (K : CochainComplex.Plus (FilteredObject.Finite.category C)) :
    IsStrictReplacement (lowerBound K) (bundled K) (comparison K) := sorry

end BoundedConstruction

namespace Resolution

/-- Construct the single-object strict resolution at supplied filtration bounds. -/
@[stacks 05TT "explicit iterated single-object resolution"]
def singleAtBounds [EnoughInjectives C] (A : FilteredObject.Finite.category C) (a b : ℤ)
    (hab : a ≤ b) (ha : A.obj.filtration.stage a = ⊤)
    (hb : A.obj.filtration.stage (b + 1) = ⊥) : Resolution (Single.source A) where
  lowerBound := 0
  complex := Single.bundled A.obj a b
  ι := Single.comparison A a b
  isStrict := Single.isStrictReplacement A a b hab ha hb

/-- Construct 05TT using only input filtration bounds and ambient injective presentations.
In particular the iteration never chooses from `Embedding.nonempty` or `Resolution.nonempty`. -/
@[stacks 05TT "single-object resolution from enough injectives"]
def singleOfEnoughInjectives [EnoughInjectives C] (A : FilteredObject.Finite.category C) :
    Resolution (Single.source A) :=
  singleAtBounds A
    (FilteredObject.Finite.FilteredInjective.Embedding.lowerBound A)
    (FilteredObject.Finite.FilteredInjective.Embedding.upperBound A)
    (FilteredObject.Finite.FilteredInjective.Embedding.lowerBound_le_upperBound A)
    (FilteredObject.Finite.FilteredInjective.Embedding.stage_lowerBound A)
    (FilteredObject.Finite.FilteredInjective.Embedding.stage_upperBound_succ A)

/-- The bounded-below strict filtered-injective resolution constructed from the supplied
ambient injective presentations, kernel/coimage horseshoes, and their coproduct total. -/
@[stacks 05TW "resolution from enough injectives"]
def ofEnoughInjectives [EnoughInjectives C]
    (K : CochainComplex.Plus (FilteredObject.Finite.category C)) : Resolution K where
  lowerBound := BoundedConstruction.lowerBound K
  complex := BoundedConstruction.bundled K
  ι := BoundedConstruction.comparison K
  isStrict := BoundedConstruction.isStrictReplacement K

/-- The resolving complex vanishes strictly below its chosen lower bound. -/
@[stacks 05TW "strict filtered-injective resolution"]
theorem strictlyGE {K : CochainComplex.Plus (FilteredObject.Finite.category C)}
    (R : Resolution K) :
    ((FilteredInjectivePlus.ι C).obj R.complex).IsStrictlyGE R.lowerBound := sorry

/-- The comparison of a strict filtered-injective resolution is monomorphic in every degree. -/
@[stacks 05TW "strict filtered-injective resolution"]
theorem termMono {K : CochainComplex.Plus (FilteredObject.Finite.category C)}
    (R : Resolution K) (n : ℤ) : Mono (R.ι.f n) := sorry

/-- The comparison of a strict filtered-injective resolution is a filtered
quasi-isomorphism. -/
@[stacks 05TW "strict filtered-injective resolution"]
theorem quasiIso {K : CochainComplex.Plus (FilteredObject.Finite.category C)}
    (R : Resolution K) :
    FilteredObject.Finite.CochainComplex.quasiIso C R.ι := sorry

/-- Every component of a strict filtered-injective resolution comparison is strict. -/
@[stacks 05TW "strict filtered-injective resolution"]
theorem termStrict {K : CochainComplex.Plus (FilteredObject.Finite.category C)}
    (R : Resolution K) (n : ℤ) :
    FilteredObject.Hom.Strict ((FilteredObject.Finite.inclusion C).map (R.ι.f n)) := sorry

/-- Every bounded-below complex of finite filtered objects admits a strict filtered-injective
resolution. -/
@[stacks 05TW "existence of strict filtered-injective resolutions"]
theorem nonempty [EnoughInjectives C]
    (K : CochainComplex.Plus (FilteredObject.Finite.category C)) :
    Nonempty (Resolution K) := ⟨ofEnoughInjectives K⟩

/-- A morphism between chosen strict filtered-injective resolutions lying over a fixed morphism
of their bounded-below source complexes. -/
@[stacks 05TU "morphism of strict filtered-injective resolutions"]
structure Map {K L : CochainComplex.Plus (FilteredObject.Finite.category C)}
    (f : K ⟶ L) (R : Resolution K) (S : Resolution L) where
  /-- The morphism between the resolving complexes. -/
  hom : (FilteredInjectivePlus.ι C).obj R.complex ⟶
    (FilteredInjectivePlus.ι C).obj S.complex
  /-- Compatibility with the two resolution comparisons. -/
  ι_naturality : R.ι ≫ hom = f.hom ≫ S.ι

namespace Map

/-- Maps of strict filtered-injective resolutions are determined by their morphisms between the
resolving complexes. -/
@[ext, stacks 05TU "extensionality of maps of strict filtered-injective resolutions"]
theorem ext {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} {m n : Map f R S}
    (h : m.hom = n.hom) : m = n := sorry

/-- The identity morphism satisfies the comparison square for a strict filtered-injective
resolution. -/
@[stacks 05TU "identity map of a strict filtered-injective resolution"]
theorem idNaturality {K : CochainComplex.Plus (FilteredObject.Finite.category C)}
    (R : Resolution K) :
    R.ι ≫ 𝟙 ((FilteredInjectivePlus.ι C).obj R.complex) =
      (𝟙 K : K ⟶ K).hom ≫ R.ι := sorry

/-- The identity morphism of a strict filtered-injective resolution. -/
@[stacks 05TU "identity map of a strict filtered-injective resolution"]
def id {K : CochainComplex.Plus (FilteredObject.Finite.category C)}
    (R : Resolution K) : Map (𝟙 K) R R where
  hom := 𝟙 ((FilteredInjectivePlus.ι C).obj R.complex)
  ι_naturality := idNaturality R

/-- The morphism underlying the identity resolution map is the identity. -/
@[simp, stacks 05TU "identity map of a strict filtered-injective resolution"]
theorem id_hom {K : CochainComplex.Plus (FilteredObject.Finite.category C)}
    (R : Resolution K) :
    (id R).hom = 𝟙 ((FilteredInjectivePlus.ι C).obj R.complex) := sorry

/-- The composite morphism satisfies the comparison square for the composite source map. -/
@[stacks 05TU "composition of maps of strict filtered-injective resolutions"]
theorem compNaturality
    {K L M : CochainComplex.Plus (FilteredObject.Finite.category C)}
    {f : K ⟶ L} {g : L ⟶ M} {R : Resolution K} {S : Resolution L}
    {T : Resolution M} (m : Map f R S) (n : Map g S T) :
    R.ι ≫ (m.hom ≫ n.hom) = (f ≫ g).hom ≫ T.ι := sorry

/-- The composite of maps of strict filtered-injective resolutions. -/
@[stacks 05TU "composition of maps of strict filtered-injective resolutions"]
def comp {K L M : CochainComplex.Plus (FilteredObject.Finite.category C)}
    {f : K ⟶ L} {g : L ⟶ M} {R : Resolution K} {S : Resolution L}
    {T : Resolution M} (m : Map f R S) (n : Map g S T) : Map (f ≫ g) R T where
  hom := m.hom ≫ n.hom
  ι_naturality := compNaturality m n

/-- The morphism underlying a composite resolution map is the composite morphism. -/
@[simp, stacks 05TU "composition of maps of strict filtered-injective resolutions"]
theorem comp_hom
    {K L M : CochainComplex.Plus (FilteredObject.Finite.category C)}
    {f : K ⟶ L} {g : L ⟶ M} {R : Resolution K} {S : Resolution L}
    {T : Resolution M} (m : Map f R S) (n : Map g S T) :
    (comp m n).hom = m.hom ≫ n.hom := sorry

/-- Reindexing a resolution map along an equality of source morphisms preserves its comparison
square. -/
@[stacks 05TU "reindexing a map of strict filtered-injective resolutions"]
theorem reindexNaturality
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f g : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (h : f = g) (m : Map f R S) :
    R.ι ≫ m.hom = g.hom ≫ S.ι := sorry

/-- Reindex a map of strict filtered-injective resolutions without changing the morphism between
resolving complexes. -/
@[stacks 05TU "reindexing a map of strict filtered-injective resolutions"]
def reindex {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f g : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (h : f = g) (m : Map f R S) : Map g R S where
  hom := m.hom
  ι_naturality := reindexNaturality h m

/-- Reindexing does not change the morphism between resolving complexes. -/
@[simp, stacks 05TU "reindexing a map of strict filtered-injective resolutions"]
theorem reindex_hom
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f g : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (h : f = g) (m : Map f R S) :
    (reindex h m).hom = m.hom := sorry

/-- Reindexing along reflexivity leaves a resolution map unchanged. -/
@[simp, stacks 05TU "reindexing a map of strict filtered-injective resolutions"]
theorem reindex_rfl
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Map f R S) :
    reindex rfl m = m := sorry

/-- The identity resolution map is a left identity after reindexing. -/
@[stacks 05TU "left identity for maps of strict filtered-injective resolutions"]
theorem id_comp
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Map f R S) :
    reindex (Category.id_comp f) (comp (id R) m) = m := sorry

/-- The identity resolution map is a right identity after reindexing. -/
@[stacks 05TU "right identity for maps of strict filtered-injective resolutions"]
theorem comp_id
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Map f R S) :
    reindex (Category.comp_id f) (comp m (id S)) = m := sorry

/-- Composition of resolution maps is associative after reindexing. -/
@[stacks 05TU "associativity of maps of strict filtered-injective resolutions"]
theorem assoc
    {K L M N : CochainComplex.Plus (FilteredObject.Finite.category C)}
    {f : K ⟶ L} {g : L ⟶ M} {h : M ⟶ N}
    {R : Resolution K} {S : Resolution L} {T : Resolution M} {U : Resolution N}
    (m : Map f R S) (n : Map g S T) (k : Map h T U) :
    reindex (Category.assoc f g h) (comp (comp m n) k) = comp m (comp n k) := sorry

/-- A morphism of bounded-below finite filtered complexes lifts between any two chosen strict
filtered-injective resolutions. -/
@[stacks 05TU "comparison map of strict filtered-injective resolutions"]
theorem nonempty
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} (f : K ⟶ L)
    (R : Resolution K) (S : Resolution L) : Nonempty (Map f R S) := sorry

end Map

/-- A morphism of bounded-below finite filtered complexes admits compatible choices of strict
filtered-injective resolutions. -/
@[stacks 05TU "functoriality of strict filtered-injective resolutions"]
theorem existsMap [EnoughInjectives C]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    ∃ (R : Resolution K) (S : Resolution L), Nonempty (Map f R S) := sorry

end Resolution

/-- Every finite filtered object admits a degree-zero filtered quasi-isomorphism to a
filtered-injective complex that vanishes in negative degrees. -/
@[stacks 05TT "filtered-injective resolution"]
theorem exists_quasiIso_single [EnoughInjectives C]
    (A : FilteredObject.Finite.category C) :
    ∃ (I : FilteredInjectivePlus C)
      (f : (CochainComplex.singleFunctor (FilteredObject.Finite.category C) (0 : ℤ)).obj A ⟶
        (FilteredInjectivePlus.ι C).obj I),
      ((FilteredInjectivePlus.ι C).obj I).IsStrictlyGE 0 ∧
        FilteredObject.Finite.CochainComplex.quasiIso C f := by
  let R := Resolution.singleOfEnoughInjectives A
  exact ⟨R.complex, R.ι, R.isStrict.strictlyGE, R.isStrict.quasiIso⟩

/-- Every finite filtered object has a degree-zero strict filtered-injective replacement. -/
@[stacks 05TT "strict filtered-injective replacement"]
theorem exists_strictReplacement_single [EnoughInjectives C]
    (A : FilteredObject.Finite.category C) :
    ∃ (I : FilteredInjectivePlus C)
      (f : (CochainComplex.singleFunctor (FilteredObject.Finite.category C) (0 : ℤ)).obj A ⟶
        (FilteredInjectivePlus.ι C).obj I),
      IsStrictReplacement 0 I f := by
  let R := Resolution.singleOfEnoughInjectives A
  exact ⟨R.complex, R.ι, R.isStrict⟩

/-- A morphism of finite filtered objects lifts to a morphism between prescribed strict
filtered-injective replacements. -/
@[stacks 05TU "strict filtered-injective replacement"]
theorem exists_map_of_strictReplacements
    {A B : FilteredObject.Finite.category C} {I J : FilteredInjectivePlus C}
    (f : A ⟶ B)
    (a : (CochainComplex.singleFunctor (FilteredObject.Finite.category C) (0 : ℤ)).obj A ⟶
      (FilteredInjectivePlus.ι C).obj I)
    (ha : IsStrictReplacement 0 I a)
    (b : (CochainComplex.singleFunctor (FilteredObject.Finite.category C) (0 : ℤ)).obj B ⟶
      (FilteredInjectivePlus.ι C).obj J) :
    ∃ g : (FilteredInjectivePlus.ι C).obj I ⟶ (FilteredInjectivePlus.ι C).obj J,
      CommSq a
        ((CochainComplex.singleFunctor (FilteredObject.Finite.category C) (0 : ℤ)).map f) g b := sorry

/-- A morphism of finite filtered objects lifts between degree-zero filtered quasi-isomorphisms
to bounded-below filtered-injective complexes. -/
@[stacks 05TU "filtered-injective comparison map"]
theorem exists_map_of_quasiIsos
    {A B : FilteredObject.Finite.category C} {I J : FilteredInjectivePlus C}
    (f : A ⟶ B)
    (a : (CochainComplex.singleFunctor (FilteredObject.Finite.category C) (0 : ℤ)).obj A ⟶
      (FilteredInjectivePlus.ι C).obj I)
    (b : (CochainComplex.singleFunctor (FilteredObject.Finite.category C) (0 : ℤ)).obj B ⟶
      (FilteredInjectivePlus.ι C).obj J)
    (hI : ((FilteredInjectivePlus.ι C).obj I).IsStrictlyGE 0)
    (hJ : ((FilteredInjectivePlus.ι C).obj J).IsStrictlyGE 0)
    (ha : FilteredObject.Finite.CochainComplex.quasiIso C a)
    (hb : FilteredObject.Finite.CochainComplex.quasiIso C b) :
    ∃ g : (FilteredInjectivePlus.ι C).obj I ⟶ (FilteredInjectivePlus.ι C).obj J,
      CommSq a
        ((CochainComplex.singleFunctor (FilteredObject.Finite.category C) (0 : ℤ)).map f) g b := sorry

end FilteredInjectivePlus

end CochainComplex
