/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.Projection
public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.Truncation
public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.Functor.Truncated
public import ReasLib.AlgebraicTopology.SimplicialSet.StdSimplex
public import ReasLib.AlgebraicTopology.SimplicialSet.Truncated.StdSimplex
public import ReasLib.CategoryTheory.Functor.IndexedCoproduct.UliftYoneda

/-!
# Standard-simplex copowers

@stack 017F

This file specializes the category-generic `indexedCoprod.uliftYoneda` calculation to copowers
by standard simplices and records the canonical identification of a copower indexed by `Δ[0]`
with its constant factor.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open SimplexCategory.Truncated
open SSet.stdSimplex
open scoped Simplicial SimplexCategory.Truncated

noncomputable section

universe w v u

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

namespace HasCopowers

/-- Copowers indexed by the zero simplex exist in every category: degreewise, the indexing
type is a singleton.  This canonical owner removes zero-simplex copower hypotheses from
downstream universal properties. -/
@[stacks 017F "canonical zero-simplex copowers"]
instance (priority := 1100) stdSimplexZero :
    HasCopowers (Δ[0] : SSet.{w}) C :=
  ⟨fun V ↦ ⟨fun Delta ↦
    @hasCoproduct_of_equiv_of_iso
      ((Δ[0] : SSet.{w}).obj Delta) PUnit.{w + 1} C _
      (fun _ : PUnit.{w + 1} ↦ V.obj Delta)
      (fun _ : (Δ[0] : SSet.{w}).obj Delta ↦ V.obj Delta)
      (inferInstance)
      (SSet.stdSimplex.zeroObjEquiv.{w} Delta)
      (fun _ ↦ Iso.refl _)⟩⟩

end HasCopowers

namespace copower

section StandardSimplex

namespace stdSimplex

variable (k : ℕ) (X : C)
variable [h : HasCopower (Δ[k] : SSet.{w}) ((const C).obj X)]

/-- Maps from the standard-simplex copower `Δ[k] × const X` are canonically equivalent to
maps from `X` into degree `k`.  This is the standard-simplex notation bridge to the
category-generic Yoneda-indexed coproduct equivalence. -/
@[stacks 017F "Lemma 14.13.4 (1)"]
noncomputable abbrev homEquiv (V : SimplicialObject C) :
    (copower (Δ[k] : SSet.{w}) ((const C).obj X) ⟶ V) ≃
      (X ⟶ V.obj (op (SimplexCategory.mk k))) :=
  @Functor.indexedCoprod.uliftYoneda.homEquiv
    _ _ _ _ (SimplexCategory.mk k) X h V

/-- The standard-simplex copower equivalence restricts the degree-`k` component to the
summand indexed by the identity simplex. -/
@[stacks 017F "standard-simplex copower equivalence formula"]
theorem homEquiv.apply {V : SimplicialObject C}
    (γ : copower (Δ[k] : SSet.{w}) ((const C).obj X) ⟶ V) :
    homEquiv k X V γ =
      Sigma.ι
          (fun _ : (Δ[k] : SSet.{w}).obj (op (SimplexCategory.mk k)) ↦
            ((const C).obj X).obj (op (SimplexCategory.mk k)))
          (SSet.stdSimplex.objEquiv.symm (𝟙 (SimplexCategory.mk k))) ≫
        γ.app (op (SimplexCategory.mk k)) := sorry

/-- The inverse map is recorded degreewise in terms of the simplex represented by each summand. -/
@[stacks 017F "standard-simplex copower inverse component"]
theorem homEquiv.symm_apply (V : SimplicialObject C)
    (f : X ⟶ V.obj (op (SimplexCategory.mk k))) (Delta : SimplexCategoryᵒᵖ) :
    ((homEquiv k X V).symm f).app Delta =
      Sigma.desc (fun g : (Δ[k] : SSet.{w}).obj Delta ↦
        f ≫ V.map (SSet.stdSimplex.objEquiv g).op) := sorry

/-- The inverse map restricted to one coproduct summand is the corresponding structure map. -/
@[reassoc, stacks 017F "standard-simplex copower inverse injection"]
theorem homEquiv.symm_apply_ι (V : SimplicialObject C)
    (f : X ⟶ V.obj (op (SimplexCategory.mk k))) (Delta : SimplexCategoryᵒᵖ)
    (g : (Δ[k] : SSet.{w}).obj Delta) :
    Sigma.ι
          (fun _ : (Δ[k] : SSet.{w}).obj Delta ↦
            ((const C).obj X).obj Delta) g ≫
        ((homEquiv k X V).symm f).app Delta =
      f ≫ V.map (SSet.stdSimplex.objEquiv g).op := sorry

/-- Standard-simplex evaluation is natural under postcomposition in the simplicial target. -/
@[stacks 017F "standard-simplex copower target naturality"]
theorem homEquiv.comp {V W : SimplicialObject C}
    (f : copower (Δ[k] : SSet.{w}) ((const C).obj X) ⟶ V) (g : V ⟶ W) :
    homEquiv k X W (f ≫ g) =
      homEquiv k X V f ≫ g.app (op (SimplexCategory.mk k)) := sorry

/-- Standard-simplex evaluation is natural in the constant object. -/
@[stacks 017F "standard-simplex copower source naturality"]
theorem homEquiv.precomp {Y : C} {V : SimplicialObject C}
    [HasCopower (Δ[k] : SSet.{w}) ((const C).obj Y)]
    (f : X ⟶ Y)
    (g : copower (Δ[k] : SSet.{w}) ((const C).obj Y) ⟶ V) :
    homEquiv k X V
        (copower.hom (Δ[k] : SSet.{w}) ((const C).map f) ≫ g) =
      f ≫ homEquiv k Y V g := sorry

end stdSimplex

end StandardSimplex

section ZeroSimplex

namespace zeroSimplex

variable (X : C)

/-- The component of the canonical section from a constant simplicial object to its
`Δ[0]`-indexed copower. -/
@[stacks 017F "zero-simplex copower section component"]
def sectionHomApp (Δ : SimplexCategoryᵒᵖ) :
    ((const C).obj X).obj Δ ⟶ (copower (Δ[0] : SSet.{w}) ((const C).obj X)).obj Δ :=
  Sigma.ι
    (fun _ : (Δ[0] : SSet.{w}).obj Δ ↦ ((const C).obj X).obj Δ)
    (SSet.stdSimplex.const 0 0 Δ)

/-- The degreewise sections of the zero-simplex copower are simplicially natural. -/
@[stacks 017F "zero-simplex copower section naturality"]
theorem sectionHomApp.naturality {Δ Δ' : SimplexCategoryᵒᵖ}
    (f : Δ ⟶ Δ') :
    ((const C).obj X).map f ≫ sectionHomApp X Δ' =
      sectionHomApp X Δ ≫
        (copower (Δ[0] : SSet.{w}) ((const C).obj X)).map f := sorry

/-- The canonical section from a constant simplicial object to its zero-simplex copower. -/
@[stacks 017F "zero-simplex copower section"]
def sectionHom :
    (const C).obj X ⟶ copower (Δ[0] : SSet.{w}) ((const C).obj X) where
  app Δ := sectionHomApp X Δ
  naturality := fun {_ _} f ↦ sectionHomApp.naturality X f

/-- The component of the bundled zero-simplex copower section is `sectionHomApp`. -/
@[simp, stacks 017F "zero-simplex copower section component formula"]
theorem sectionHom_app (Δ : SimplexCategoryᵒᵖ) :
    (sectionHom X).app Δ = sectionHomApp X Δ := sorry

/-- The zero-simplex copower projection followed by its section is the identity. -/
@[stacks 017F "zero-simplex copower projection-section inverse"]
theorem sectionHom.projection_comp :
    copower.projection ((const C).obj X) (Δ[0] : SSet.{w}) ≫ sectionHom X =
      𝟙 (copower (Δ[0] : SSet.{w}) ((const C).obj X)) := sorry

/-- The zero-simplex copower section followed by its projection is the identity. -/
@[stacks 017F "zero-simplex copower section-projection inverse"]
theorem sectionHom.comp_projection :
    sectionHom X ≫
        copower.projection ((const C).obj X) (Δ[0] : SSet.{w}) =
      𝟙 ((const C).obj X) := sorry

/-- The zero-simplex copower of a constant simplicial object is canonically that constant
simplicial object. -/
@[stacks 017F "zero-simplex copower identification"]
noncomputable def iso :
    copower (Δ[0] : SSet.{w}) ((const C).obj X) ≅ (const C).obj X where
  hom := copower.projection ((const C).obj X) (Δ[0] : SSet.{w})
  inv := sectionHom X
  hom_inv_id := sectionHom.projection_comp X
  inv_hom_id := sectionHom.comp_projection X

/-- The zero-simplex copower isomorphism is natural in the constant object. -/
@[stacks 017F "zero-simplex copower identification naturality"]
theorem iso.naturality {Y : C}
    (f : X ⟶ Y) :
    (iso X).hom ≫ (const C).map f =
      copower.hom (Δ[0] : SSet.{w}) ((const C).map f) ≫
        (iso Y).hom := sorry

/-- The inverse zero-simplex copower identification, equivalently its section, is natural in
the constant object. -/
@[stacks 017F "zero-simplex copower identification inverse naturality"]
theorem iso.inv_naturality {Y : C}
    (f : X ⟶ Y) :
    (const C).map f ≫ (iso Y).inv =
      (iso X).inv ≫ copower.hom (Δ[0] : SSet.{w}) ((const C).map f) := sorry

end zeroSimplex

end ZeroSimplex

end copower

namespace Truncated.copower

section StandardSimplex

namespace stdSimplex

variable {n k : ℕ} (hk : k ≤ n) (X : C)
variable [Truncated.HasCopower ((SSet.truncation n).obj (Δ[k] : SSet.{w}))
  ((Functor.const (SimplexCategory.Truncated n)ᵒᵖ).obj X)]

/-- Maps from the truncated standard-simplex copower are canonically maps from the constant
factor into degree `k` of the target.  This is the notation bridge from truncated standard
simplices to the category-generic Yoneda equivalence up to index isomorphism. -/
@[stacks 017F "Lemma 14.13.4 (2), truncated copower"]
noncomputable abbrev homEquiv (W : SimplicialObject.Truncated C n) :
    (Truncated.copower ((SSet.truncation n).obj (Δ[k] : SSet.{w}))
        ((Functor.const (SimplexCategory.Truncated n)ᵒᵖ).obj X) ⟶ W) ≃
      (X ⟶ W.obj (op ⦋k,hk⦌ₙ)) :=
  Functor.indexedCoprod.uliftYoneda.homEquiv.ofIso
    ⦋k,hk⦌ₙ (SSet.Truncated.stdSimplex.iso hk) X W

/-- The truncated standard-simplex copower equivalence restricts the degree-`k` component to
the summand indexed by the identity simplex. -/
@[stacks 017F "truncated standard-simplex copower equivalence formula"]
theorem homEquiv.apply {W : SimplicialObject.Truncated C n}
    (γ : Truncated.copower ((SSet.truncation n).obj (Δ[k] : SSet.{w}))
      ((Functor.const (SimplexCategory.Truncated n)ᵒᵖ).obj X) ⟶ W) :
    homEquiv hk X W γ =
      Sigma.ι
          (fun _ : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj (op ⦋k,hk⦌ₙ) ↦
            ((Functor.const (SimplexCategory.Truncated n)ᵒᵖ).obj X).obj (op ⦋k,hk⦌ₙ))
          (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋k⦌)) ≫
        γ.app (op ⦋k,hk⦌ₙ) := sorry

/-- The truncated inverse map is assembled from the canonical truncated simplex map. -/
@[stacks 017F "truncated standard-simplex copower inverse component"]
theorem homEquiv.symm_apply (W : SimplicialObject.Truncated C n)
    (f : X ⟶ W.obj (op ⦋k,hk⦌ₙ)) (Delta : (SimplexCategory.Truncated n)ᵒᵖ) :
    ((homEquiv hk X W).symm f).app Delta =
      Sigma.desc
        (fun u : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj Delta ↦
          f ≫ W.map (SSet.Truncated.stdSimplex.simplexMap hk Delta u)) := sorry

/-- The truncated inverse restricted to one summand computes the associated structure map. -/
@[reassoc, stacks 017F "truncated standard-simplex copower inverse injection"]
theorem homEquiv.symm_apply_ι (W : SimplicialObject.Truncated C n)
    (f : X ⟶ W.obj (op ⦋k,hk⦌ₙ)) (Delta : (SimplexCategory.Truncated n)ᵒᵖ)
    (u : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj Delta) :
    Sigma.ι
          (fun _ : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj Delta ↦
            ((Functor.const (SimplexCategory.Truncated n)ᵒᵖ).obj X).obj Delta) u ≫
        ((homEquiv hk X W).symm f).app Delta =
      f ≫ W.map (SSet.Truncated.stdSimplex.simplexMap hk Delta u) := sorry

/-- Truncated standard-simplex evaluation is natural under postcomposition in the target. -/
@[stacks 017F "truncated standard-simplex copower target naturality"]
theorem homEquiv.comp {W Z : SimplicialObject.Truncated C n}
    (f : Truncated.copower ((SSet.truncation n).obj (Δ[k] : SSet.{w}))
      ((Functor.const (SimplexCategory.Truncated n)ᵒᵖ).obj X) ⟶ W)
    (g : W ⟶ Z) :
    homEquiv hk X Z (f ≫ g) =
      homEquiv hk X W f ≫ g.app (op ⦋k,hk⦌ₙ) := sorry

/-- Truncated standard-simplex evaluation is natural in the constant object. -/
@[stacks 017F "truncated standard-simplex copower source naturality"]
theorem homEquiv.precomp {Y : C} {W : SimplicialObject.Truncated C n}
    [Truncated.HasCopower ((SSet.truncation n).obj (Δ[k] : SSet.{w}))
      ((Functor.const (SimplexCategory.Truncated n)ᵒᵖ).obj Y)]
    (f : X ⟶ Y)
    (g : Truncated.copower ((SSet.truncation n).obj (Δ[k] : SSet.{w}))
      ((Functor.const (SimplexCategory.Truncated n)ᵒᵖ).obj Y) ⟶ W) :
    homEquiv hk X W
        (Truncated.copower.hom ((SSet.truncation n).obj (Δ[k] : SSet.{w}))
          ((Functor.const (SimplexCategory.Truncated n)ᵒᵖ).map f) ≫ g) =
      f ≫ homEquiv hk Y W g := sorry

end stdSimplex

end StandardSimplex

end Truncated.copower

namespace copower

section TruncatedStandardSimplex

namespace truncation

namespace stdSimplex

variable {n k : ℕ} (hk : k ≤ n) (X : C)
variable [HasCopower (Δ[k] : SSet.{w}) ((const C).obj X)]

/-- Source-faithful truncated form of the standard-simplex copower equivalence: maps from the
truncation of the full copower are maps from `X` into degree `k`. -/
@[stacks 017F "Lemma 14.13.4 (2)"]
def homEquiv (W : SimplicialObject.Truncated C n) :
    ((truncation n).obj (copower (Δ[k] : SSet.{w}) ((const C).obj X)) ⟶ W) ≃
      (X ⟶ W.obj (op ⦋k,hk⦌ₙ)) :=
  ((copower.truncation.iso n (Δ[k] : SSet.{w}) ((const C).obj X)).homCongr
      (Iso.refl W)).trans
    (Truncated.copower.stdSimplex.homEquiv hk X W)

/-- The restriction-form standard-simplex equivalence evaluates on the identity-indexed
coproduct summand in degree `k`. -/
@[stacks 017F "restricted standard-simplex copower equivalence formula"]
theorem homEquiv.apply {W : SimplicialObject.Truncated C n}
    (γ : (truncation n).obj (copower (Δ[k] : SSet.{w}) ((const C).obj X)) ⟶ W) :
    homEquiv hk X W γ =
      Sigma.ι
          (fun _ : (Δ[k] : SSet.{w}).obj (op ⦋k⦌) ↦
            ((const C).obj X).obj (op ⦋k⦌))
          (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋k⦌)) ≫
        γ.app (op ⦋k,hk⦌ₙ) := sorry

/-- The restriction-form inverse is assembled from the same truncated simplex map. -/
@[stacks 017F "restricted standard-simplex copower inverse component"]
theorem homEquiv.symm_apply (W : SimplicialObject.Truncated C n)
    (f : X ⟶ W.obj (op ⦋k,hk⦌ₙ)) (Delta : (SimplexCategory.Truncated n)ᵒᵖ) :
    ((homEquiv hk X W).symm f).app Delta =
      Sigma.desc
        (fun u : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj Delta ↦
          f ≫ W.map (SSet.Truncated.stdSimplex.simplexMap hk Delta u)) := sorry

/-- The restriction-form inverse restricted to one summand computes the associated structure map. -/
@[reassoc, stacks 017F "restricted standard-simplex copower inverse injection"]
theorem homEquiv.symm_apply_ι (W : SimplicialObject.Truncated C n)
    (f : X ⟶ W.obj (op ⦋k,hk⦌ₙ)) (Delta : (SimplexCategory.Truncated n)ᵒᵖ)
    (u : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj Delta) :
    Sigma.ι
          (fun _ : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj Delta ↦
            ((Functor.const (SimplexCategory.Truncated n)ᵒᵖ).obj X).obj Delta) u ≫
        ((homEquiv hk X W).symm f).app Delta =
      f ≫ W.map (SSet.Truncated.stdSimplex.simplexMap hk Delta u) := sorry

/-- Restriction-form standard-simplex evaluation is natural under postcomposition in the
truncated target. -/
@[stacks 017F "restricted standard-simplex copower target naturality"]
theorem homEquiv.comp
    {W Z : SimplicialObject.Truncated C n}
    (f : (truncation n).obj (copower (Δ[k] : SSet.{w}) ((const C).obj X)) ⟶ W)
    (g : W ⟶ Z) :
    homEquiv hk X Z (f ≫ g) =
      homEquiv hk X W f ≫ g.app (op ⦋k,hk⦌ₙ) := sorry

/-- Restriction-form standard-simplex evaluation is natural in the constant object. -/
@[stacks 017F "restricted standard-simplex copower source naturality"]
theorem homEquiv.precomp {Y : C} {W : SimplicialObject.Truncated C n}
    [HasCopower (Δ[k] : SSet.{w}) ((const C).obj Y)]
    (f : X ⟶ Y)
    (g : (truncation n).obj (copower (Δ[k] : SSet.{w}) ((const C).obj Y)) ⟶ W) :
    homEquiv hk X W
        ((truncation n).map (copower.hom (Δ[k] : SSet.{w}) ((const C).map f)) ≫ g) =
      f ≫ homEquiv hk Y W g := sorry

end stdSimplex

end truncation

end TruncatedStandardSimplex

end copower

end CategoryTheory.SimplicialObject
