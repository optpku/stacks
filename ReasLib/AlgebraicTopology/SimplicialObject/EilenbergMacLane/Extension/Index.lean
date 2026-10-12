/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.ChainComplex.Disk
public import Mathlib.AlgebraicTopology.SimplicialObject.Split
public import ReasLib.AlgebraicTopology.SimplexCategory.EpiMono
public import ReasLib.AlgebraicTopology.SimplicialObject.EilenbergMacLane.Functor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Eilenberg-MacLane extension objects and summand indices

This file owns the Dold-Kan image of the disk complex together with the two-family summand index
and its partial pullback along simplex operators.  The index and pull use Mathlib's initial-face
(`d₀`) convention; the source final-face convention is transported in the separate
`Extension.SourceIndex` leaf.  The degreewise coproduct and short-complex APIs are separate
downstream leaves.

@stack 0192
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology HomologicalComplex
open scoped Simplicial DoldKan

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject.eilenbergMacLane.extension

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜] [HasZeroObject 𝒜]

section

variable [HasFiniteCoproducts 𝒜]

/-- The Dold-Kan image of the two-term identity complex, functorial in the coefficient object. -/
@[stacks 0192 "Eilenberg-MacLane extension object functor"]
noncomputable abbrev functor (k : ℕ) : 𝒜 ⥤ SimplicialObject 𝒜 :=
  ChainComplex.disk.functor 𝒜 k ⋙ AlgebraicTopology.DoldKan.Γ₀

/-- The Dold-Kan image of the two-term identity complex. -/
@[stacks 0192 "Eilenberg-MacLane extension object"]
noncomputable abbrev object (A : 𝒜) (k : ℕ) : SimplicialObject 𝒜 :=
  (functor (𝒜 := 𝒜) k).obj A

/-- Evaluating the extension functor gives the Dold-Kan image `object A k`. -/
@[simp, stacks 0192 "Eilenberg-MacLane extension functor object formula"]
theorem functor_obj (k : ℕ) (A : 𝒜) :
    (functor (𝒜 := 𝒜) k).obj A = object A k := sorry

/-- The extension functor maps a coefficient morphism by applying `Γ₀` to the corresponding
map of two-term identity complexes. -/
@[simp, stacks 0192 "Eilenberg-MacLane extension functor map formula"]
theorem functor_map (k : ℕ) {A B : 𝒜} (f : A ⟶ B) :
    (functor (𝒜 := 𝒜) k).map f =
      AlgebraicTopology.DoldKan.Γ₀.map (ChainComplex.disk.map k f) := sorry

/-- Degree-`n` summands of the Eilenberg-MacLane extension: epimorphisms to degree `k` or to
degree `k + 1`. -/
@[stacks 0192 "Eilenberg-MacLane extension summand index"]
abbrev Index (k n : ℕ) :=
  SimplexCategory.EpiHom ⦋n⦌ ⦋k⦌ ⊕
    SimplexCategory.EpiHom ⦋n⦌ ⦋k + 1⦌

namespace Index

/-- A degree-`k` epimorphism, viewed as a lower summand of the extension. -/
@[stacks 0192 "lower Eilenberg-MacLane extension summand"]
abbrev lower {k n : ℕ}
    (a : SimplexCategory.EpiHom ⦋n⦌ ⦋k⦌) : Index k n :=
  .inl a

/-- A degree-`k + 1` epimorphism, viewed as an upper summand of the extension. -/
@[stacks 0192 "upper Eilenberg-MacLane extension summand"]
abbrev upper {k n : ℕ}
    (a : SimplexCategory.EpiHom ⦋n⦌ ⦋k + 1⦌) : Index k n :=
  .inr a

/-- The common map `[n] ⟶ [k + 1]` represented by an extension index. -/
@[stacks 0192 "d₀-oriented Eilenberg-MacLane extension index map"]
def hom {k n : ℕ} : Index k n → (⦋n⦌ ⟶ ⦋k + 1⦌)
  | .inl a => a.hom ≫ SimplexCategory.δ 0
  | .inr a => a.hom

/-- The common map represented by a lower extension summand. -/
@[simp, stacks 0192 "lower extension summand map formula"]
theorem hom_lower {k n : ℕ}
    (a : SimplexCategory.EpiHom ⦋n⦌ ⦋k⦌) :
    (lower a).hom = a.hom ≫ SimplexCategory.δ 0 := sorry

/-- The common map represented by an upper extension summand. -/
@[simp, stacks 0192 "upper extension summand map formula"]
theorem hom_upper {k n : ℕ}
    (a : SimplexCategory.EpiHom ⦋n⦌ ⦋k + 1⦌) :
    (upper a).hom = a.hom := sorry

/-- An extension summand is determined by its common map to `[k + 1]`. -/
@[stacks 0192 "extension summand index injectivity"]
theorem hom_injective {k n : ℕ} :
    Function.Injective (hom (k := k) (n := n)) := sorry

/-- The extension index viewed as an index in the canonical Dold-Kan splitting. -/
@[stacks 0192 "Eilenberg-MacLane extension splitting index"]
def toSplitIndex {k n : ℕ} :
    Index k n → SimplicialObject.Splitting.IndexSet (Opposite.op ⦋n⦌)
  | .inl a => ⟨Opposite.op ⦋k⦌, ⟨a.hom, a.property⟩⟩
  | .inr a => ⟨Opposite.op ⦋k + 1⦌, ⟨a.hom, a.property⟩⟩

/-- A lower extension summand selects the corresponding degree-`k` Dold-Kan summand. -/
@[simp, stacks 0192 "lower extension splitting-index formula"]
theorem toSplitIndex_lower {k n : ℕ}
    (a : SimplexCategory.EpiHom ⦋n⦌ ⦋k⦌) :
    (lower a).toSplitIndex = ⟨Opposite.op ⦋k⦌, ⟨a.hom, a.property⟩⟩ := sorry

/-- An upper extension summand selects the corresponding degree-`k + 1` Dold-Kan summand. -/
@[simp, stacks 0192 "upper extension splitting-index formula"]
theorem toSplitIndex_upper {k n : ℕ}
    (a : SimplexCategory.EpiHom ⦋n⦌ ⦋k + 1⦌) :
    (upper a).toSplitIndex = ⟨Opposite.op ⦋k + 1⦌, ⟨a.hom, a.property⟩⟩ := sorry

/-- Pull an extension index along `[m] ⟶ [n]`. A result of `none` means that the corresponding
summand is mapped to zero. -/
@[stacks 0192 "d₀-oriented partial reindexing of Eilenberg-MacLane extension summands"]
noncomputable def pull {k m n : ℕ} (a : Index k n)
    (φ : ⦋m⦌ ⟶ ⦋n⦌) : Option (Index k m) :=
  if hfull : Function.Surjective ((φ ≫ hom a).toOrderHom) then
    some (.inr
      ⟨φ ≫ hom a, (SimplexCategory.epi_iff_surjective).2 hfull⟩)
  else if hlen : (⦋k + 1⦌ : SimplexCategory).len =
      (image (φ ≫ hom a)).len + 1 then
    if _ : (image.ι (φ ≫ hom a)).toOrderHom 0 ≠ 0 then
      some (.inl
        ⟨factorThruImage (φ ≫ hom a) ≫
            eqToHom
              (SimplexCategory.ext
                (Nat.add_right_cancel hlen.symm)),
          inferInstance⟩)
    else
      none
  else
    none

/-- A successful pull represents the composite simplex operator. -/
@[stacks 0192 "successful extension-index pull formula"]
theorem pull.hom {k m n : ℕ} (a : Index k n)
    (φ : ⦋m⦌ ⟶ ⦋n⦌) {b : Index k m}
    (h : a.pull φ = some b) :
    b.hom = φ ≫ a.hom := sorry

/-- Pulling succeeds with `b` exactly when `b` represents the composite simplex operator. -/
@[stacks 0192 "successful extension summand pull criterion"]
theorem pull_eq_some_iff {k m n : ℕ} (a : Index k n)
    (φ : ⦋m⦌ ⟶ ⦋n⦌) (b : Index k m) :
    a.pull φ = some b ↔ b.hom = φ ≫ a.hom := sorry

/-- Pulling returns `none` exactly when no extension summand represents the composite simplex
operator. -/
@[stacks 0192 "zero extension summand pull criterion"]
theorem pull_eq_none_iff {k m n : ℕ} (a : Index k n)
    (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    a.pull φ = none ↔
      ¬ ∃ b : Index k m, b.hom = φ ≫ a.hom := sorry

/-- A successful pull has a unique resulting extension summand. -/
@[stacks 0192 "uniqueness of an extension-index pull"]
theorem pull_unique {k m n : ℕ} (a : Index k n)
    (φ : ⦋m⦌ ⟶ ⦋n⦌) {b c : Index k m}
    (hb : a.pull φ = some b) (hc : a.pull φ = some c) :
    b = c := sorry

/-- Pulling an extension index along the identity leaves it unchanged. -/
@[simp, stacks 0192 "identity extension-index pull"]
theorem pull.id {k n : ℕ} (a : Index k n) :
    a.pull (𝟙 _) = some a := sorry

/-- Pulling extension indices is compatible with composition of simplex operators. -/
@[stacks 0192 "composition of extension-index pulls"]
theorem pull.comp {k l m n : ℕ} (a : Index k n)
    (φ : ⦋m⦌ ⟶ ⦋n⦌) (ψ : ⦋l⦌ ⟶ ⦋m⦌) :
    a.pull (ψ ≫ φ) =
      (a.pull φ).bind fun b => b.pull ψ := sorry

/-- A successful extension-index pull agrees with the pull in the canonical Dold-Kan
splitting. -/
@[stacks 0192 "extension-index pull and splitting pull comparison"]
theorem toSplitIndex.pull {k m n : ℕ} (a : Index k n)
    (φ : ⦋m⦌ ⟶ ⦋n⦌) {b : Index k m}
    (h : a.pull φ = some b) :
    (a.toSplitIndex).pull φ.op = b.toSplitIndex := sorry

end Index

end

end CategoryTheory.SimplicialObject.eilenbergMacLane.extension
