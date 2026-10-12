/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplexCategory.Truncated.Finite
public import ReasLib.CategoryTheory.Functor.IndexedProduct.Coyoneda
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 017M

# Costandard simplices and truncation

The costandard simplex represented by `d : SimplexCategory` is the canonical covariant
representable `coyoneda.obj (op d)`.  This module records how such a representable and its
coyoneda-indexed products restrict to a truncated simplex category.
-/

@[expose] public section

open CategoryTheory.Limits Opposite
open scoped Simplicial SimplexCategory.Truncated

noncomputable section

universe v u

namespace CategoryTheory.CosimplicialObject.Truncated

namespace coyoneda

/-- Bundle a morphism of underlying simplices as a morphism in the truncated simplex
category. -/
@[stacks 017M "truncated costandard indexing map"]
def objEquiv.forward {k : ℕ} (d Δ : SimplexCategory.Truncated k)
    (f : (coyoneda.obj (op d.obj)).obj Δ.obj) :
    (coyoneda.obj (op d)).obj Δ :=
  (ObjectProperty.fullyFaithfulι _).homEquiv.symm f

/-- Forget a morphism in the truncated simplex category to its underlying simplex map. -/
@[stacks 017M "truncated costandard indexing inverse"]
def objEquiv.inverse {k : ℕ} (d Δ : SimplexCategory.Truncated k)
    (f : (coyoneda.obj (op d)).obj Δ) :
    (coyoneda.obj (op d.obj)).obj Δ.obj :=
  (ObjectProperty.fullyFaithfulι _).homEquiv f

/-- Restricting the costandard simplex represented by the underlying simplex of `d` gives,
degreewise, the covariant representable of `d` in the full truncated simplex category. -/
@[stacks 017M "truncated costandard indexing equivalence"]
def objEquiv {k : ℕ} (d Δ : SimplexCategory.Truncated k) :
    (coyoneda.obj (op d.obj)).obj Δ.obj ≃ (coyoneda.obj (op d)).obj Δ :=
  (ObjectProperty.fullyFaithfulι _).homEquiv.symm

/-- The truncated costandard indexing equivalence applies by bundling the underlying simplex
map. -/
@[simp, stacks 017M "truncated costandard indexing equivalence application"]
theorem objEquiv.apply {k : ℕ} (d Δ : SimplexCategory.Truncated k)
    (f : (coyoneda.obj (op d.obj)).obj Δ.obj) :
    objEquiv d Δ f = objEquiv.forward d Δ f := sorry

/-- The inverse truncated costandard indexing equivalence forgets to the underlying simplex
map. -/
@[simp, stacks 017M "truncated costandard indexing inverse application"]
theorem objEquiv.symm_apply {k : ℕ} (d Δ : SimplexCategory.Truncated k)
    (f : (coyoneda.obj (op d)).obj Δ) :
    (objEquiv d Δ).symm f = objEquiv.inverse d Δ f := sorry

/-- The truncated costandard indexing equivalences are natural in the target simplex. -/
@[stacks 017M "truncated costandard indexing naturality"]
theorem objEquiv.naturality {k : ℕ} (d : SimplexCategory.Truncated k)
    {Δ Δ' : SimplexCategory.Truncated k} (f : Δ ⟶ Δ') :
    ((CosimplicialObject.truncation k).obj
          (coyoneda.obj (op d.obj) : CosimplicialObject (Type))).map f ≫
        (objEquiv d Δ').toIso.hom =
      (objEquiv d Δ).toIso.hom ≫
        (coyoneda.obj (op d) : CosimplicialObject.Truncated (Type) k).map f := sorry

/-- Restriction of a costandard simplex to the truncated simplex category is canonically the
costandard simplex represented there by the same bundled object. -/
@[stacks 017M "truncation of a costandard simplex"]
noncomputable def iso {k : ℕ} (d : SimplexCategory.Truncated k) :
    (CosimplicialObject.truncation k).obj
      (coyoneda.obj (op d.obj) : CosimplicialObject (Type)) ≅
      (coyoneda.obj (op d) : CosimplicialObject.Truncated (Type) k) :=
  NatIso.ofComponents (fun Δ ↦ (objEquiv d Δ).toIso) (objEquiv.naturality d)

/-- The component of the truncated costandard-simplex comparison is the isomorphism associated
to the underlying indexing equivalence. -/
@[simp, stacks 017M "truncated costandard-simplex comparison component"]
theorem iso_app {k : ℕ} (d Δ : SimplexCategory.Truncated k) :
    (iso d).app Δ = (objEquiv d Δ).toIso := sorry

end coyoneda

end CategoryTheory.CosimplicialObject.Truncated

namespace CategoryTheory.SimplicialObject.Truncated

variable {C : Type u} [Category.{v} C]

namespace coyoneda

namespace truncation

/-- Restricting a coyoneda-indexed product along the truncated simplex inclusion supplies the
corresponding indexed product over the truncated representable.  Thus downstream comparison
maps only need the untruncated existence owner; the truncated owner is inferred canonically. -/
@[stacks 017M "indexed products over a truncated costandard simplex"]
instance (priority := 40) hasIndexedProd {k : ℕ}
    (d : SimplexCategory.Truncated k) (V : SimplicialObject C)
    [Functor.HasIndexedProd (coyoneda.obj (op d.obj)) V] :
    Functor.HasIndexedProd (coyoneda.obj (op d))
      ((SimplicialObject.truncation k).obj V) :=
  ⟨fun Δ ↦
    @hasProduct_of_equiv_of_iso _ _ _ _
      (fun _ : (coyoneda.obj (op d.obj)).obj Δ.obj ↦ V.obj (op Δ.obj))
      (fun _ : (coyoneda.obj (op d)).obj Δ ↦ V.obj (op Δ.obj))
      (Functor.HasIndexedProd.hasProduct
        (U := coyoneda.obj (op d.obj)) (V := V) Δ.obj)
      (CosimplicialObject.Truncated.coyoneda.objEquiv d Δ).symm
      (fun _ ↦ Iso.refl _)⟩

/-- The constant-valued form of `truncation.hasIndexedProd`.  This bridge exposes the
mathematical equality between restricting a constant simplicial object and the constant
truncated simplicial object to typeclass search. -/
@[stacks 017M "constant indexed products over a truncated costandard simplex"]
instance (priority := 40) constHasIndexedProd {k : ℕ}
    (d : SimplexCategory.Truncated k) (X : C)
    [Functor.HasIndexedProd (coyoneda.obj (op d.obj))
      ((Functor.const SimplexCategoryᵒᵖ).obj X)] :
    Functor.HasIndexedProd (coyoneda.obj (op d))
      ((Functor.const (SimplexCategory.Truncated k)ᵒᵖ).obj X) :=
  ⟨fun Δ ↦
    (hasIndexedProd d ((Functor.const SimplexCategoryᵒᵖ).obj X)).hasProduct Δ⟩

end truncation

section Comparison

variable {k : ℕ} (d : SimplexCategory.Truncated k) (X : C)
variable
  [Functor.HasIndexedProd (coyoneda.obj (op d.obj))
    ((Functor.const SimplexCategoryᵒᵖ).obj X)]

/-- The degreewise reindexing isomorphism comparing a restricted coyoneda-indexed product
with its truncated counterpart. -/
@[stacks 017M "truncated coyoneda-indexed product component"]
noncomputable def isoApp (Δ : (SimplexCategory.Truncated k)ᵒᵖ) :
    ((SimplicialObject.truncation k).obj
          (Functor.indexedProd (coyoneda.obj (op d.obj))
            ((Functor.const SimplexCategoryᵒᵖ).obj X))).obj Δ ≅
      (Functor.indexedProd (coyoneda.obj (op d))
          ((Functor.const (SimplexCategory.Truncated k)ᵒᵖ).obj X)).obj Δ :=
  (Pi.whiskerEquiv
      (CosimplicialObject.Truncated.coyoneda.objEquiv d (unop Δ))
      (fun _ ↦ Iso.refl X) :
    (∏ᶜ fun _ : (coyoneda.obj (op d.obj)).obj (unop Δ).obj ↦ X) ≅
      (∏ᶜ fun _ : (coyoneda.obj (op d)).obj (unop Δ) ↦ X))

/-- The degreewise reindexing comparisons are natural in the truncated simplex. -/
@[stacks 017M "truncated coyoneda-indexed product component naturality"]
theorem isoApp.naturality {Δ Δ' : (SimplexCategory.Truncated k)ᵒᵖ} (f : Δ ⟶ Δ') :
    ((SimplicialObject.truncation k).obj
          (Functor.indexedProd (coyoneda.obj (op d.obj))
            ((Functor.const SimplexCategoryᵒᵖ).obj X))).map f ≫
        (isoApp d X Δ').hom =
      (isoApp d X Δ).hom ≫
        (Functor.indexedProd (coyoneda.obj (op d))
          ((Functor.const (SimplexCategory.Truncated k)ᵒᵖ).obj X)).map f := sorry

/-- Restricting a coyoneda-indexed product represented by the underlying simplex of `d`
agrees with the indexed product represented by `d` in the truncated simplex category. -/
@[stacks 017M "truncated coyoneda-indexed product comparison"]
noncomputable def iso :
    (SimplicialObject.truncation k).obj
        (Functor.indexedProd (coyoneda.obj (op d.obj))
          ((Functor.const SimplexCategoryᵒᵖ).obj X)) ≅
      Functor.indexedProd (coyoneda.obj (op d))
        ((Functor.const (SimplexCategory.Truncated k)ᵒᵖ).obj X) :=
  NatIso.ofComponents (isoApp d X) (isoApp.naturality d X)

/-- The component of the indexed-product restriction comparison is its degreewise reindexing
isomorphism. -/
@[simp, stacks 017M "truncated indexed-product comparison component"]
theorem iso_app (Δ : (SimplexCategory.Truncated k)ᵒᵖ) :
    (iso d X).app Δ = isoApp d X Δ := sorry

/-- The restriction comparison reindexes the projection at `g` by the inverse of the
degreewise equivalence between the two representable indexing types. -/
@[stacks 017M "truncated coyoneda-indexed product projection"]
theorem iso.hom_app_π
    (Δ : SimplexCategory.Truncated k) (g : (coyoneda.obj (op d)).obj Δ) :
    (iso d X).hom.app (op Δ) ≫
        Pi.π (fun _ : (coyoneda.obj (op d)).obj Δ ↦ X) g =
      Pi.π (fun _ : (coyoneda.obj (op d.obj)).obj Δ.obj ↦ X)
        ((CosimplicialObject.Truncated.coyoneda.objEquiv d Δ).symm g) := sorry

/-- The inverse restriction comparison reindexes a projection at an underlying simplex map by
the degreewise equivalence with maps in the truncated simplex category. -/
@[stacks 017M "inverse truncated coyoneda-indexed product projection"]
theorem iso.inv_app_π
    (Δ : SimplexCategory.Truncated k)
    (g : (coyoneda.obj (op d.obj)).obj Δ.obj) :
    (iso d X).inv.app (op Δ) ≫
        Pi.π (fun _ : (coyoneda.obj (op d.obj)).obj Δ.obj ↦ X) g =
      Pi.π (fun _ : (coyoneda.obj (op d)).obj Δ ↦ X)
        (CosimplicialObject.Truncated.coyoneda.objEquiv d Δ g) := sorry

/-- The restriction of the coyoneda-indexed product represents maps from evaluation at the
truncated simplex `d` to `X`.  This is the natural-in-source owner of the truncated Hom
equivalence; the comparison `iso d X` transports the generic representation back to the
untruncated indexed product used by restriction. -/
@[stacks 017M "representability of truncated coyoneda-indexed products"]
noncomputable def representableBy :
    (((evaluation (SimplexCategory.Truncated k)ᵒᵖ C).obj (op d)).op ⋙
        yoneda.obj X).RepresentableBy
      ((SimplicialObject.truncation k).obj
        (Functor.indexedProd (coyoneda.obj (op d.obj))
          ((Functor.const SimplexCategoryᵒᵖ).obj X))) :=
  Functor.representableByUliftFunctorEquiv
    ((Functor.indexedProd.coyoneda.representableBy d X).ofIsoObj (iso d X))

/-- Maps from a truncated simplicial object into the restriction of a coyoneda-indexed product
are canonically maps from its value at the representing truncated simplex. -/
@[stacks 017M "truncated coyoneda-indexed product Hom equivalence"]
noncomputable def homEquiv (W : SimplicialObject.Truncated C k) :
    (W ⟶ (SimplicialObject.truncation k).obj
      (Functor.indexedProd (coyoneda.obj (op d.obj))
        ((Functor.const SimplexCategoryᵒᵖ).obj X))) ≃
      (W.obj (op d) ⟶ X) :=
  (representableBy d X).homEquiv

end Comparison

section HomEquiv

variable {k : ℕ} {d : SimplexCategory.Truncated k} {X : C}
variable
  [Functor.HasIndexedProd (coyoneda.obj (op d.obj))
    ((Functor.const SimplexCategoryᵒᵖ).obj X)]

/-- The truncated coyoneda-indexed product Hom equivalence evaluates at `d` and projects to
the factor indexed by the identity of the underlying simplex. -/
@[stacks 017M "truncated coyoneda-indexed product evaluation"]
theorem homEquiv.apply {W : SimplicialObject.Truncated C k}
    (γ : W ⟶ (SimplicialObject.truncation k).obj
      (Functor.indexedProd (coyoneda.obj (op d.obj))
        ((Functor.const SimplexCategoryᵒᵖ).obj X))) :
    homEquiv d X W γ =
      γ.app (op d) ≫
        Pi.π (fun _ : (coyoneda.obj (op d.obj)).obj d.obj ↦ X) (𝟙 d.obj) := sorry

end HomEquiv

section HomEquivFormula

variable {k : ℕ} (d : SimplexCategory.Truncated k) {X : C}
variable
  [Functor.HasIndexedProd (coyoneda.obj (op d.obj))
    ((Functor.const SimplexCategoryᵒᵖ).obj X)]

/-- The inverse truncated coyoneda Hom equivalence is the ordinary coyoneda inverse followed
by the inverse truncation comparison. -/
@[stacks 017M "truncated coyoneda Hom equivalence inverse formula"]
theorem homEquiv.symm_apply (W : SimplicialObject.Truncated C k)
    (f : W.obj (op d) ⟶ X) (Δ : (SimplexCategory.Truncated k)ᵒᵖ) :
    ((homEquiv d X W).symm f).app Δ =
      Pi.lift (fun g : (coyoneda.obj (op d)).obj (unop Δ) ↦
        W.map (op g) ≫ f) ≫ (iso d X).inv.app Δ := sorry

/-- Projecting the inverse truncated coyoneda Hom equivalence at a truncated simplex map
recovers the corresponding structure map of `W`, followed by the given morphism. -/
@[reassoc, stacks 017M "truncated coyoneda Hom equivalence inverse projection formula"]
theorem homEquiv.symm_apply_π (W : SimplicialObject.Truncated C k)
    (f : W.obj (op d) ⟶ X) (Δ : SimplexCategory.Truncated k)
    (g : (coyoneda.obj (op d)).obj Δ) :
    ((homEquiv d X W).symm f).app (op Δ) ≫
        Pi.π (fun _ : (coyoneda.obj (op d.obj)).obj Δ.obj ↦ X)
          ((CosimplicialObject.Truncated.coyoneda.objEquiv d Δ).symm g) =
      W.map (op g) ≫ f := sorry

/-- The truncated coyoneda Hom equivalence is natural by precomposition in its source
simplicial object. -/
@[stacks 017M "truncated coyoneda Hom equivalence source naturality"]
theorem homEquiv.precomp {V W : SimplicialObject.Truncated C k}
    (a : V ⟶ W)
    (γ : W ⟶ (SimplicialObject.truncation k).obj
      (Functor.indexedProd (coyoneda.obj (op d.obj))
        ((Functor.const SimplexCategoryᵒᵖ).obj X))) :
    homEquiv d X V (a ≫ γ) = a.app (op d) ≫ homEquiv d X W γ := sorry

end HomEquivFormula

section HomEquivPostcomp

variable {k : ℕ} (d : SimplexCategory.Truncated k) {X Y : C}
variable
  [Functor.HasIndexedProd (coyoneda.obj (op d.obj))
    ((Functor.const SimplexCategoryᵒᵖ).obj X)]
  [Functor.HasIndexedProd (coyoneda.obj (op d.obj))
    ((Functor.const SimplexCategoryᵒᵖ).obj Y)]

/-- The truncated coyoneda Hom equivalence is natural by postcomposition in its target
object. -/
@[stacks 017M "truncated coyoneda Hom equivalence target naturality"]
theorem homEquiv.postcomp {W : SimplicialObject.Truncated C k}
    (f : X ⟶ Y)
    (γ : W ⟶ (SimplicialObject.truncation k).obj
      (Functor.indexedProd (coyoneda.obj (op d.obj))
        ((Functor.const SimplexCategoryᵒᵖ).obj X))) :
    homEquiv d Y W
        (γ ≫ (SimplicialObject.truncation k).map
          (Functor.indexedProd.hom (coyoneda.obj (op d.obj))
            ((Functor.const SimplexCategoryᵒᵖ).map f))) =
      homEquiv d X W γ ≫ f := sorry

end HomEquivPostcomp

end coyoneda

end CategoryTheory.SimplicialObject.Truncated

namespace CategoryTheory

section SpecializationChecks

variable {C : Type u} [Category.{v} C] {k : ℕ}
variable (d : SimplexCategory.Truncated k) (X : C)
variable (W : SimplicialObject.Truncated C k)

section FiniteProducts

variable [HasFiniteProducts C]

-- The source-facing Chap14 hypothesis supplies both exact indexed products automatically.

end FiniteProducts

section PositivePowers

variable [HasPositivePowers X]

-- Positive powers suffice because both representable indexing functors are finite and nonempty.

end PositivePowers

end SpecializationChecks

end CategoryTheory
