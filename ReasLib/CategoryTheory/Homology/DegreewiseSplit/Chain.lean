module

public import ReasLib.CategoryTheory.Homology.ChainShift
public import ReasLib.CategoryTheory.Homology.DegreewiseSplit
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Degreewise Split Short Complexes of Chain Complexes

This file supplies the chain-complex counterpart of `CochainComplex.homOfDegreewiseSplit`.
-/

@[expose] public section

open CategoryTheory HomologicalComplex

universe v u

namespace ChainComplex

noncomputable section

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace homOfDegreewiseSplit

/-- The unshifted coordinate of the degree-`n` connecting map associated to a degreewise
splitting of a short complex of chain complexes. -/
@[stacks 011D "chain degreewise connecting-map coordinate"]
def coordinate (S : ShortComplex (ChainComplex C ℤ))
    (σ : ShortComplex.DegreewiseSplitting S) (n : ℤ) :
    S.X₃.X n ⟶ S.X₁.X (n - 1) :=
  (σ n).s ≫ S.X₂.d n (n - 1) ≫ (σ (n - 1)).r

/-- The degree-`n` component of the connecting map associated to a degreewise splitting of a
short complex of chain complexes. -/
@[stacks 011D "chain degreewise connecting-map component"]
def component (S : ShortComplex (ChainComplex C ℤ))
    (σ : ShortComplex.DegreewiseSplitting S) (n : ℤ) :
    S.X₃.X n ⟶ (S.X₁⟦(-1 : ℤ)⟧).X n :=
  coordinate S σ n ≫ (Shift.MinusOne.xIso S.X₁ n).inv

/-- Transporting the shifted component back to its unshifted coordinate recovers
`coordinate`. -/
theorem component_comp_xIso (S : ShortComplex (ChainComplex C ℤ))
    (σ : ShortComplex.DegreewiseSplitting S) (n : ℤ) :
    component S σ n ≫ (Shift.MinusOne.xIso S.X₁ n).hom = coordinate S σ n := sorry

/-- The components of the connecting map commute with the chain differentials. -/
theorem comm (S : ShortComplex (ChainComplex C ℤ))
    (σ : ShortComplex.DegreewiseSplitting S) (i j : ℤ)
    (hij : (ComplexShape.down ℤ).Rel i j) :
    component S σ i ≫ (S.X₁⟦(-1 : ℤ)⟧).d i j =
      S.X₃.d i j ≫ component S σ j := sorry

end homOfDegreewiseSplit

/-- The canonical map `S.X₃ ⟶ S.X₁⟦-1⟧` attached to a degreewise split short complex of
chain complexes. -/
@[stacks 011D]
def homOfDegreewiseSplit (S : ShortComplex (ChainComplex C ℤ))
    (σ : ShortComplex.DegreewiseSplitting S) : S.X₃ ⟶ S.X₁⟦(-1 : ℤ)⟧ where
  f := homOfDegreewiseSplit.component S σ
  comm' := homOfDegreewiseSplit.comm S σ

namespace homOfDegreewiseSplit

/-- The canonical chain connecting map has the raw component exposed by `component`. -/
theorem component_eq (S : ShortComplex (ChainComplex C ℤ))
    (σ : ShortComplex.DegreewiseSplitting S) (n : ℤ) :
    (ChainComplex.homOfDegreewiseSplit S σ).f n =
      ChainComplex.homOfDegreewiseSplit.component S σ n := sorry

end homOfDegreewiseSplit

/-- Under the standard degree identification, the degree-`n` component of
`homOfDegreewiseSplit` is `σₙ.s ≫ d ≫ σₙ₋₁.r`. -/
@[simp]
theorem homOfDegreewiseSplit_f (S : ShortComplex (ChainComplex C ℤ))
    (σ : ShortComplex.DegreewiseSplitting S) (n : ℤ) :
    (homOfDegreewiseSplit S σ).f n ≫ (Shift.MinusOne.xIso S.X₁ n).hom =
      (σ n).s ≫ S.X₂.d n (n - 1) ≫ (σ (n - 1)).r := sorry

end

end ChainComplex

namespace CategoryTheory.ShortComplex.DegreewiseSplitting

noncomputable section

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {S T : ShortComplex (ChainComplex C ℤ)}

/-- The connecting maps of two chosen degreewise splittings form a commuting square with the
prescribed maps on the outer terms. -/
@[stacks 01A3 "compatibility with degreewise connecting maps"]
abbrev BoundaryCommSq (σ : DegreewiseSplitting S) (τ : DegreewiseSplitting T)
    (left : S.X₁ ⟶ T.X₁) (right : S.X₃ ⟶ T.X₃) : Prop :=
  CommSq (ChainComplex.homOfDegreewiseSplit S σ) right (left⟦(-1 : ℤ)⟧')
    (ChainComplex.homOfDegreewiseSplit T τ)

/-- Compatible boundary data between degreewise split short complexes consists of maps on the
outer terms whose connecting-map square commutes. -/
@[stacks 01A3 "boundary data between degreewise split short complexes"]
structure BoundaryHom (σ : DegreewiseSplitting S) (τ : DegreewiseSplitting T) where
  /-- The map on the first terms. -/
  left : S.X₁ ⟶ T.X₁
  /-- The map on the third terms. -/
  right : S.X₃ ⟶ T.X₃
  /-- Compatibility of the outer maps with the connecting maps. -/
  comm : BoundaryCommSq σ τ left right

/-- Compatible boundary data is determined by its two outer maps. -/
@[ext]
theorem BoundaryHom.ext {σ : DegreewiseSplitting S} {τ : DegreewiseSplitting T}
    {p q : BoundaryHom σ τ} (hleft : p.left = q.left)
    (hright : p.right = q.right) : p = q := sorry

/-- The degree-`n` middle map induced by compatible maps on the outer terms of two degreewise
split short complexes. -/
@[stacks 01A3 "middle map between degreewise split short complexes"]
def middleApp (σ : DegreewiseSplitting S) (τ : DegreewiseSplitting T)
    (left : S.X₁ ⟶ T.X₁) (right : S.X₃ ⟶ T.X₃) (n : ℤ) :
    S.X₂.X n ⟶ T.X₂.X n :=
  ((σ n).r ≫ left.f n ≫ T.f.f n : S.X₂.X n ⟶ T.X₂.X n) +
    (S.g.f n ≫ right.f n ≫ (τ n).s : S.X₂.X n ⟶ T.X₂.X n)

/-- The induced middle components commute with the chain differentials when the connecting-map
square commutes. -/
theorem middleApp_comm (σ : DegreewiseSplitting S) (τ : DegreewiseSplitting T)
    (left : S.X₁ ⟶ T.X₁) (right : S.X₃ ⟶ T.X₃)
    (hboundary : BoundaryCommSq σ τ left right) (i j : ℤ)
    (hij : (ComplexShape.down ℤ).Rel i j) :
    middleApp σ τ left right i ≫ T.X₂.d i j =
      S.X₂.d i j ≫ middleApp σ τ left right j := sorry

/-- The chain map on middle terms induced by a commuting square of connecting maps. -/
@[stacks 01A3 "middle chain map between degreewise split short complexes"]
def middle (σ : DegreewiseSplitting S) (τ : DegreewiseSplitting T)
    (left : S.X₁ ⟶ T.X₁) (right : S.X₃ ⟶ T.X₃)
    (hboundary : BoundaryCommSq σ τ left right) : S.X₂ ⟶ T.X₂ where
  f := middleApp σ τ left right
  comm' := middleApp_comm σ τ left right hboundary

/-- The components of the induced middle chain map are given by `middleApp`. -/
@[simp]
theorem middle_f (σ : DegreewiseSplitting S) (τ : DegreewiseSplitting T)
    (left : S.X₁ ⟶ T.X₁) (right : S.X₃ ⟶ T.X₃)
    (hboundary : BoundaryCommSq σ τ left right) (n : ℤ) :
    (middle σ τ left right hboundary).f n = middleApp σ τ left right n := sorry

/-- The induced middle map makes the square on the first terms commute. -/
theorem middle.comm₁₂ (σ : DegreewiseSplitting S) (τ : DegreewiseSplitting T)
    (left : S.X₁ ⟶ T.X₁) (right : S.X₃ ⟶ T.X₃)
    (hboundary : BoundaryCommSq σ τ left right) :
    left ≫ T.f = S.f ≫ middle σ τ left right hboundary := sorry

/-- The induced middle map makes the square on the third terms commute. -/
theorem middle.comm₂₃ (σ : DegreewiseSplitting S) (τ : DegreewiseSplitting T)
    (left : S.X₁ ⟶ T.X₁) (right : S.X₃ ⟶ T.X₃)
    (hboundary : BoundaryCommSq σ τ left right) :
    middle σ τ left right hboundary ≫ T.g = S.g ≫ right := sorry

/-- The induced middle map followed by the target retraction is the source retraction followed
by the prescribed map on the first terms. -/
@[reassoc (attr := simp), stacks 01A3 "middle map retraction formula"]
theorem middle.comp_retraction (σ : DegreewiseSplitting S) (τ : DegreewiseSplitting T)
    (left : S.X₁ ⟶ T.X₁) (right : S.X₃ ⟶ T.X₃)
    (hboundary : BoundaryCommSq σ τ left right) (n : ℤ) :
    (middle σ τ left right hboundary).f n ≫ (τ n).r =
      (σ n).r ≫ left.f n := sorry

/-- The source section followed by the induced middle map is the prescribed map on the third
terms followed by the target section. -/
@[reassoc (attr := simp), stacks 01A3 "middle map section formula"]
theorem middle.section_comp (σ : DegreewiseSplitting S) (τ : DegreewiseSplitting T)
    (left : S.X₁ ⟶ T.X₁) (right : S.X₃ ⟶ T.X₃)
    (hboundary : BoundaryCommSq σ τ left right) (n : ℤ) :
    (σ n).s ≫ (middle σ τ left right hboundary).f n =
      right.f n ≫ (τ n).s := sorry

/-- A commuting square of connecting maps induces a morphism of the degreewise split short
complexes. -/
@[stacks 01A3 "morphism between degreewise split short complexes"]
def hom (σ : DegreewiseSplitting S) (τ : DegreewiseSplitting T)
    (left : S.X₁ ⟶ T.X₁) (right : S.X₃ ⟶ T.X₃)
    (hboundary : BoundaryCommSq σ τ left right) : S ⟶ T where
  τ₁ := left
  τ₂ := middle σ τ left right hboundary
  τ₃ := right
  comm₁₂ := middle.comm₁₂ σ τ left right hboundary
  comm₂₃ := middle.comm₂₃ σ τ left right hboundary

/-- The first component of the induced short-complex morphism is the prescribed left map. -/
@[simp]
theorem hom.τ₁ (σ : DegreewiseSplitting S) (τ : DegreewiseSplitting T)
    (left : S.X₁ ⟶ T.X₁) (right : S.X₃ ⟶ T.X₃)
    (hboundary : BoundaryCommSq σ τ left right) :
    (hom σ τ left right hboundary).τ₁ = left := sorry

/-- The middle component of the induced short-complex morphism is the canonical middle map. -/
@[simp]
theorem hom.τ₂ (σ : DegreewiseSplitting S) (τ : DegreewiseSplitting T)
    (left : S.X₁ ⟶ T.X₁) (right : S.X₃ ⟶ T.X₃)
    (hboundary : BoundaryCommSq σ τ left right) :
    (hom σ τ left right hboundary).τ₂ = middle σ τ left right hboundary := sorry

/-- The third component of the induced short-complex morphism is the prescribed right map. -/
@[simp]
theorem hom.τ₃ (σ : DegreewiseSplitting S) (τ : DegreewiseSplitting T)
    (left : S.X₁ ⟶ T.X₁) (right : S.X₃ ⟶ T.X₃)
    (hboundary : BoundaryCommSq σ τ left right) :
    (hom σ τ left right hboundary).τ₃ = right := sorry

/-- The induced short-complex morphism respects the chosen splittings in every degree. -/
@[stacks 01A3 "induced morphism respects degreewise splittings"]
theorem hom.respects (σ : DegreewiseSplitting S) (τ : DegreewiseSplitting T)
    (left : S.X₁ ⟶ T.X₁) (right : S.X₃ ⟶ T.X₃)
    (hboundary : BoundaryCommSq σ τ left right) :
    (hom σ τ left right hboundary).RespectsDegreewiseSplittings σ τ := sorry

/-- A morphism respecting chosen degreewise splittings induces a commuting square between the
associated connecting maps. -/
@[stacks 01A3 "naturality of degreewise connecting maps"]
theorem boundaryCommSq (σ : DegreewiseSplitting S) (τ : DegreewiseSplitting T)
    {φ : S ⟶ T} (respects : φ.RespectsDegreewiseSplittings σ τ) :
    BoundaryCommSq σ τ φ.τ₁ φ.τ₃ := sorry

/-- A splitting-compatible short-complex morphism is determined by its maps on the outer terms. -/
theorem hom.unique (σ : DegreewiseSplitting S) (τ : DegreewiseSplitting T)
    (left : S.X₁ ⟶ T.X₁) (right : S.X₃ ⟶ T.X₃)
    (hboundary : BoundaryCommSq σ τ left right) (φ : S ⟶ T)
    (hleft : φ.τ₁ = left) (hright : φ.τ₃ = right)
    (respects : φ.RespectsDegreewiseSplittings σ τ) :
    φ = hom σ τ left right hboundary := sorry

namespace BoundaryHom

/-- Extract the compatible boundary data of a morphism preserving chosen degreewise
splittings. -/
@[stacks 01A3 "boundary data of a degreewise-splitting morphism"]
def ofHom {σ : DegreewiseSplitting S} {τ : DegreewiseSplitting T}
    (φ : Hom σ τ) : BoundaryHom σ τ where
  left := φ.1.τ₁
  right := φ.1.τ₃
  comm := boundaryCommSq σ τ φ.2

/-- Extend compatible boundary data to the canonical morphism preserving the chosen degreewise
splittings. -/
@[stacks 01A3 "extension of compatible boundary data"]
def toHom {σ : DegreewiseSplitting S} {τ : DegreewiseSplitting T}
    (p : BoundaryHom σ τ) : Hom σ τ :=
  ⟨hom σ τ p.left p.right p.comm,
    hom.respects σ τ p.left p.right p.comm⟩

/-- Extracting the left boundary map recovers the first component of the morphism. -/
@[simp]
theorem ofHom_left {σ : DegreewiseSplitting S} {τ : DegreewiseSplitting T}
    (φ : Hom σ τ) : (ofHom φ).left = φ.1.τ₁ := sorry

/-- Extracting the right boundary map recovers the third component of the morphism. -/
@[simp]
theorem ofHom_right {σ : DegreewiseSplitting S} {τ : DegreewiseSplitting T}
    (φ : Hom σ τ) : (ofHom φ).right = φ.1.τ₃ := sorry

/-- The first component of the extension is its prescribed left boundary map. -/
@[simp]
theorem toHom_τ₁ {σ : DegreewiseSplitting S} {τ : DegreewiseSplitting T}
    (p : BoundaryHom σ τ) : (toHom p).1.τ₁ = p.left := sorry

/-- The middle component of the extension is the canonical middle map. -/
@[simp]
theorem toHom_τ₂ {σ : DegreewiseSplitting S} {τ : DegreewiseSplitting T}
    (p : BoundaryHom σ τ) :
    (toHom p).1.τ₂ = middle σ τ p.left p.right p.comm := sorry

/-- The third component of the extension is its prescribed right boundary map. -/
@[simp]
theorem toHom_τ₃ {σ : DegreewiseSplitting S} {τ : DegreewiseSplitting T}
    (p : BoundaryHom σ τ) : (toHom p).1.τ₃ = p.right := sorry

/-- Extending the boundary data of a splitting-compatible morphism recovers that morphism. -/
@[simp]
theorem toHom_ofHom {σ : DegreewiseSplitting S} {τ : DegreewiseSplitting T}
    (φ : Hom σ τ) : toHom (ofHom φ) = φ := sorry

/-- Taking boundary data after its canonical extension recovers the original boundary data. -/
@[simp]
theorem ofHom_toHom {σ : DegreewiseSplitting S} {τ : DegreewiseSplitting T}
    (p : BoundaryHom σ τ) : ofHom (toHom p) = p := sorry

/-- Identity boundary data for a chosen degreewise splitting. -/
@[stacks 01A3 "identity boundary data"]
def id (σ : DegreewiseSplitting S) : BoundaryHom σ σ :=
  ofHom (Hom.id σ)

/-- Composition of compatible boundary data. -/
@[stacks 01A3 "composition of compatible boundary data"]
def comp {R : ShortComplex (ChainComplex C ℤ)}
    {σ : DegreewiseSplitting S} {τ : DegreewiseSplitting T}
    {υ : DegreewiseSplitting R} (p : BoundaryHom σ τ)
    (q : BoundaryHom τ υ) : BoundaryHom σ υ :=
  ofHom (Hom.comp (toHom p) (toHom q))

/-- The left map of identity boundary data is the identity. -/
@[simp]
theorem id_left (σ : DegreewiseSplitting S) : (id σ).left = 𝟙 S.X₁ := sorry

/-- The right map of identity boundary data is the identity. -/
@[simp]
theorem id_right (σ : DegreewiseSplitting S) : (id σ).right = 𝟙 S.X₃ := sorry

/-- The left map of a composite is the composite of the left maps. -/
@[simp]
theorem comp_left {R : ShortComplex (ChainComplex C ℤ)}
    {σ : DegreewiseSplitting S} {τ : DegreewiseSplitting T}
    {υ : DegreewiseSplitting R} (p : BoundaryHom σ τ)
    (q : BoundaryHom τ υ) : (comp p q).left = p.left ≫ q.left := sorry

/-- The right map of a composite is the composite of the right maps. -/
@[simp]
theorem comp_right {R : ShortComplex (ChainComplex C ℤ)}
    {σ : DegreewiseSplitting S} {τ : DegreewiseSplitting T}
    {υ : DegreewiseSplitting R} (p : BoundaryHom σ τ)
    (q : BoundaryHom τ υ) : (comp p q).right = p.right ≫ q.right := sorry

end BoundaryHom

/-- Morphisms preserving chosen degreewise splittings are classified by their compatible maps on
the two outer terms. -/
@[stacks 01A3 "classification of degreewise-splitting morphisms by boundary data"]
def homEquiv (σ : DegreewiseSplitting S) (τ : DegreewiseSplitting T) :
    Hom σ τ ≃ BoundaryHom σ τ where
  toFun := BoundaryHom.ofHom
  invFun := BoundaryHom.toHom
  left_inv := BoundaryHom.toHom_ofHom
  right_inv := BoundaryHom.ofHom_toHom

/-- The classification equivalence sends a morphism to its boundary data. -/
@[simp]
theorem homEquiv_apply (σ : DegreewiseSplitting S) (τ : DegreewiseSplitting T)
    (φ : Hom σ τ) : homEquiv σ τ φ = BoundaryHom.ofHom φ := sorry

/-- The inverse classification equivalence canonically extends compatible boundary data. -/
@[simp]
theorem homEquiv_symm_apply (σ : DegreewiseSplitting S) (τ : DegreewiseSplitting T)
    (p : BoundaryHom σ τ) :
    (homEquiv σ τ).symm p = BoundaryHom.toHom p := sorry

/-- A chain map on the middle terms satisfying the two short-complex squares and the two
splitting equations is the induced middle map. -/
theorem middle.unique (σ : DegreewiseSplitting S) (τ : DegreewiseSplitting T)
    (left : S.X₁ ⟶ T.X₁) (right : S.X₃ ⟶ T.X₃)
    (hboundary : BoundaryCommSq σ τ left right) (m : S.X₂ ⟶ T.X₂)
    (hleft : S.f ≫ m = left ≫ T.f) (hright : m ≫ T.g = S.g ≫ right)
    (respects : ∀ n,
      m.f n ≫ (τ n).r = (σ n).r ≫ left.f n ∧
        (σ n).s ≫ m.f n = right.f n ≫ (τ n).s) :
    m = middle σ τ left right hboundary := sorry

/-- Compatible maps on the outer terms extend uniquely to a splitting-compatible morphism of
short complexes. -/
@[stacks 01A3 "universal property of degreewise split short complexes"]
theorem hom.existsUnique (σ : DegreewiseSplitting S) (τ : DegreewiseSplitting T)
    (left : S.X₁ ⟶ T.X₁) (right : S.X₃ ⟶ T.X₃)
    (hboundary : BoundaryCommSq σ τ left right) :
    ∃! φ : S ⟶ T,
      φ.τ₁ = left ∧ φ.τ₃ = right ∧ φ.RespectsDegreewiseSplittings σ τ := sorry

/-- Compatible maps on the outer terms determine a unique middle chain map satisfying both
short-complex squares and both splitting equations. -/
theorem middle.existsUnique (σ : DegreewiseSplitting S) (τ : DegreewiseSplitting T)
    (left : S.X₁ ⟶ T.X₁) (right : S.X₃ ⟶ T.X₃)
    (hboundary : BoundaryCommSq σ τ left right) :
    ∃! m : S.X₂ ⟶ T.X₂,
      S.f ≫ m = left ≫ T.f ∧ m ≫ T.g = S.g ≫ right ∧
        ∀ n,
          m.f n ≫ (τ n).r = (σ n).r ≫ left.f n ∧
            (σ n).s ≫ m.f n = right.f n ≫ (τ n).s := sorry

end

end CategoryTheory.ShortComplex.DegreewiseSplitting

namespace CategoryTheory.ShortComplex.ShortExact

noncomputable section

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S : ShortComplex (ChainComplex C ℤ)}

/-- A short exact sequence of chain complexes together with a section in every degree determines
the corresponding family of degreewise splittings. -/
@[stacks 011D "degreewise splitting induced by sections"]
noncomputable def splittingOfSection (hS : S.ShortExact)
    (s : ∀ n : ℤ, S.X₃.X n ⟶ S.X₂.X n)
    (hs : ∀ n : ℤ, s n ≫ S.g.f n = 𝟙 (S.X₃.X n)) :
    DegreewiseSplitting S :=
  fun n ↦
    Splitting.ofExactOfSection (S.degreewise n)
      (((HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS n).exact)
      (s n) (hs n)
      (((HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS n).mono_f)

namespace splittingOfSection

/-- The section component of the induced degreewise splitting is the prescribed section. -/
@[simp, stacks 011D "section of the induced degreewise splitting"]
theorem section_eq (hS : S.ShortExact)
    (s : ∀ n : ℤ, S.X₃.X n ⟶ S.X₂.X n)
    (hs : ∀ n : ℤ, s n ≫ S.g.f n = 𝟙 (S.X₃.X n)) (n : ℤ) :
    (hS.splittingOfSection s hs n).s = s n := sorry

end splittingOfSection

end

end CategoryTheory.ShortComplex.ShortExact
