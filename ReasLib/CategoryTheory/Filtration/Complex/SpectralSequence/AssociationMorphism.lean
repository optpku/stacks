module

public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence.PageZeroMorphism

/-!
# Morphisms of Associated Spectral Sequences

This file packages spectral-sequence morphisms compatible with a filtered-complex morphism and
provides their identity, composition, uniqueness, existence, and first-page computation API.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FilteredComplex

/-- A spectral-sequence morphism is compatible with a filtered-complex morphism relative to
chosen associations when it commutes with their zeroth-page graded-piece comparisons. This is
the representation-independent compatibility notion used by general functoriality. -/
@[stacks 012O "compatible morphism of associated spectral sequences"]
def Association.IsCompatible {K L : FilteredComplex C}
    {E E' : CohomologicalSpectralSequence C 0}
    (A : Association K E) (B : Association L E')
    (α : K ⟶ L) (φ : E ⟶ E') : Prop :=
  Page.Zero.IsCompatible A.toComparison B.toComparison α φ

namespace Association.IsCompatible

/-- Identity morphisms are compatible with any fixed association. -/
@[stacks 012O "identity map of associated spectral sequences"]
theorem id {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    (A : Association K E) :
    Association.IsCompatible A A (𝟙 K) (𝟙 E) := sorry

/-- Compatible morphisms between associated spectral sequences are closed under composition. -/
@[stacks 012O "composition of associated spectral-sequence maps"]
theorem comp {K L M : FilteredComplex C}
    {E E' E'' : CohomologicalSpectralSequence C 0}
    (A : Association K E) (B : Association L E') (D : Association M E'')
    {α : K ⟶ L} {β : L ⟶ M} {φ : E ⟶ E'} {ψ : E' ⟶ E''}
    (hφ : Association.IsCompatible A B α φ)
    (hψ : Association.IsCompatible B D β ψ) :
    Association.IsCompatible A D (α ≫ β) (φ ≫ ψ) := sorry

/-- Two spectral-sequence morphisms compatible with the same associated filtered-complex map
are equal. -/
@[stacks 012O "uniqueness of compatible associated spectral-sequence maps"]
theorem hom_ext {K L : FilteredComplex C}
    {E E' : CohomologicalSpectralSequence C 0}
    (A : Association K E) (B : Association L E') (α : K ⟶ L)
    {φ ψ : E ⟶ E'} (hφ : Association.IsCompatible A B α φ)
    (hψ : Association.IsCompatible A B α ψ) :
    φ = ψ := sorry

/-- Stacks 012O: a filtered-complex morphism induces a unique compatible morphism between
spectral sequences equipped with chosen associations. -/
@[stacks 012O "canonical morphism of associated spectral sequences"]
theorem existsUnique {K L : FilteredComplex C}
    {E E' : CohomologicalSpectralSequence C 0}
    (A : Association K E) (B : Association L E') (α : K ⟶ L) :
    ∃! φ : E ⟶ E', Association.IsCompatible A B α φ := sorry

end Association.IsCompatible

/-- An explicitly supplied morphism between associated spectral sequences over a fixed
filtered-complex morphism. The morphism is data; only its compatibility is proof-valued. -/
@[stacks 012O "morphism of associated spectral sequences"]
structure Association.Hom {K L : FilteredComplex C}
    {E E' : CohomologicalSpectralSequence C 0}
    (A : Association K E) (B : Association L E') (α : K ⟶ L) where
  /-- The underlying morphism of cohomological spectral sequences. -/
  hom : E ⟶ E'
  /-- Compatibility with the filtered-complex morphism on the zeroth page. -/
  compatible : Association.IsCompatible A B α hom

namespace Association.Hom

/-- The identity morphism of an associated spectral sequence. -/
@[stacks 012O "identity morphism of associated spectral sequences"]
def id {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    (A : Association K E) : Association.Hom A A (𝟙 K) where
  hom := 𝟙 E
  compatible := Association.IsCompatible.id A

/-- The underlying spectral-sequence map of the identity association morphism is the identity.
-/
@[simp, stacks 012O "identity map of associated spectral sequences"]
theorem id_hom {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    (A : Association K E) :
    (id A).hom = 𝟙 E := sorry

/-- The composite of explicitly supplied compatible morphisms. -/
@[stacks 012O "composition of associated spectral-sequence morphisms"]
def comp {K L M : FilteredComplex C}
    {E E' E'' : CohomologicalSpectralSequence C 0}
    {A : Association K E} {B : Association L E'} {D : Association M E''}
    {α : K ⟶ L} {β : L ⟶ M}
    (f : Association.Hom A B α) (g : Association.Hom B D β) :
    Association.Hom A D (α ≫ β) where
  hom := f.hom ≫ g.hom
  compatible := Association.IsCompatible.comp A B D f.compatible g.compatible

/-- The underlying spectral-sequence map of a composite association morphism is the composite.
-/
@[simp, stacks 012O "composition of associated spectral-sequence maps"]
theorem comp_hom {K L M : FilteredComplex C}
    {E E' E'' : CohomologicalSpectralSequence C 0}
    {A : Association K E} {B : Association L E'} {D : Association M E''}
    {α : K ⟶ L} {β : L ⟶ M}
    (f : Association.Hom A B α) (g : Association.Hom B D β) :
    (comp f g).hom = f.hom ≫ g.hom := sorry

/-- Compatible association morphisms are determined by their underlying spectral-sequence
morphisms. -/
@[ext, stacks 012O "extensionality of associated spectral-sequence morphisms"]
theorem ext {K L : FilteredComplex C}
    {E E' : CohomologicalSpectralSequence C 0}
    {A : Association K E} {B : Association L E'} {α : K ⟶ L}
    {f g : Association.Hom A B α} (h : f.hom = g.hom) :
    f = g := sorry

/-- For a fixed filtered-complex morphism, compatible association morphisms are unique. -/
@[stacks 012O "uniqueness of associated spectral-sequence morphisms"]
theorem unique {K L : FilteredComplex C}
    {E E' : CohomologicalSpectralSequence C 0}
    {A : Association K E} {B : Association L E'} {α : K ⟶ L}
    (f g : Association.Hom A B α) :
    f = g := sorry

/-- Compatible association morphisms over a fixed filtered-complex morphism form a subsingleton. -/
instance {K L : FilteredComplex C}
    {E E' : CohomologicalSpectralSequence C 0}
    {A : Association K E} {B : Association L E'} {α : K ⟶ L} :
    Subsingleton (Association.Hom A B α) := sorry

/-- A compatible association morphism exists over every filtered-complex morphism. This is kept
proposition-valued so that no concrete map is selected from deferred existence proofs. -/
@[stacks 012O "existence of an associated spectral-sequence morphism"]
theorem nonempty {K L : FilteredComplex C}
    {E E' : CohomologicalSpectralSequence C 0}
    (A : Association K E) (B : Association L E') (α : K ⟶ L) :
    Nonempty (Association.Hom A B α) := sorry

/-- The first-page comparison carried by associated spectral sequences is natural for an induced
morphism of filtered complexes. -/
@[reassoc, stacks 012O "naturality of the induced first-page map"]
theorem pageOne_naturality {K L : FilteredComplex C}
    {E E' : CohomologicalSpectralSequence C 0}
    {A : Association K E} {B : Association L E'} {α : K ⟶ L}
    (φ : Association.Hom A B α) (p q : ℤ) :
    (φ.hom.hom 1).f (p, q) ≫ (B.pageOneIso p q).hom =
      (A.pageOneIso p q).hom ≫
        HomologicalComplex.homologyMap (gradedPieceMap α p) (p + q) := sorry

/-- Inverse naturality of the first-page comparison carried by associated spectral sequences. -/
@[reassoc, stacks 012O "inverse naturality of the induced first-page map"]
theorem pageOne_inv_naturality {K L : FilteredComplex C}
    {E E' : CohomologicalSpectralSequence C 0}
    {A : Association K E} {B : Association L E'} {α : K ⟶ L}
    (φ : Association.Hom A B α) (p q : ℤ) :
    HomologicalComplex.homologyMap (gradedPieceMap α p) (p + q) ≫
        (B.pageOneIso p q).inv =
      (A.pageOneIso p q).inv ≫ (φ.hom.hom 1).f (p, q) := sorry

/-- Inverting the target first-page comparison recovers the underlying page component from the
map on graded-piece homology. This is the computation-oriented form of
`Association.Hom.pageOne_naturality`. -/
@[reassoc, stacks 012O "computation of the induced first-page map"]
theorem pageOne_naturality_inv {K L : FilteredComplex C}
    {E E' : CohomologicalSpectralSequence C 0}
    {A : Association K E} {B : Association L E'} {α : K ⟶ L}
    (φ : Association.Hom A B α) (p q : ℤ) :
    (A.pageOneIso p q).hom ≫
        HomologicalComplex.homologyMap (gradedPieceMap α p) (p + q) ≫
        (B.pageOneIso p q).inv =
      (φ.hom.hom 1).f (p, q) := sorry

end Association.Hom

end FilteredComplex

end CategoryTheory
