/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Reindex.MapIso.Naturality

/-!
# Coherence of cartesian-functor reindexing comparisons

This module records compatibility with identity and composition of cartesian based functors and
with identity and specified composition of base morphisms.
-/

@[expose] public section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

universe uS₁ vS₁ uS₂ vS₂ uS₃ vS₃

namespace CartesianBasedFunctor

variable {S₁ : Type uS₁} {S₂ : Type uS₂} [Category.{vS₁} S₁] [Category.{vS₂} S₂]
variable {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C}

/-- The forward reindexing comparison for a composite cartesian based functor is the composite
of the two individual comparisons. -/
theorem Reindex.mapIso.comp
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C}
    (F : CartesianBasedFunctor p₁ p₂) (G : CartesianBasedFunctor p₂ p₃)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage) (χ₃ : p₃.Cleavage)
    {U V : C} (f : V ⟶ U) (x : p₁.Fiber U) :
    Reindex.mapIso (F.comp G) χ₁ χ₃ f x =
      Reindex.mapIso G χ₂ χ₃ f ((F.fiberFunctor U).obj x) ≪≫
        (G.fiberFunctor V).mapIso (Reindex.mapIso F χ₁ χ₂ f x) := sorry

/-- The forward reindexing comparison for a composite cartesian based functor is the composite
of the two individual comparison maps. -/
theorem Reindex.mapIso.comp.hom
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C}
    (F : CartesianBasedFunctor p₁ p₂) (G : CartesianBasedFunctor p₂ p₃)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage) (χ₃ : p₃.Cleavage)
    {U V : C} (f : V ⟶ U) (x : p₁.Fiber U) :
    (Reindex.mapIso (F.comp G) χ₁ χ₃ f x).hom =
      (Reindex.mapIso G χ₂ χ₃ f ((F.fiberFunctor U).obj x)).hom ≫
        (G.fiberFunctor V).map (Reindex.mapIso F χ₁ χ₂ f x).hom := sorry

/-- The inverse reindexing comparison for a composite cartesian based functor is the reverse
composite of the two individual inverse comparisons. -/
theorem Reindex.mapIso.comp.inv
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C}
    (F : CartesianBasedFunctor p₁ p₂) (G : CartesianBasedFunctor p₂ p₃)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage) (χ₃ : p₃.Cleavage)
    {U V : C} (f : V ⟶ U) (x : p₁.Fiber U) :
    (Reindex.mapIso (F.comp G) χ₁ χ₃ f x).inv =
      (G.fiberFunctor V).map (Reindex.mapIso F χ₁ χ₂ f x).inv ≫
        (Reindex.mapIso G χ₂ χ₃ f ((F.fiberFunctor U).obj x)).inv := sorry

/-- The reindexing comparison of the identity cartesian based functor is the identity
isomorphism. -/
@[simp]
theorem Reindex.mapIso.id (χ₁ : p₁.Cleavage) {U V : C}
    (f : V ⟶ U) (x : p₁.Fiber U) :
    Reindex.mapIso (CartesianBasedFunctor.id p₁) χ₁ χ₁ f x =
      Iso.refl ((f⁎[χ₁]).obj x) := sorry

/-- The reindexing comparison of a cartesian based functor is compatible with composition.

This is the universe-polymorphic component form of pseudonaturality: the target composition
comparison followed by the comparisons over `f` and `g` agrees with the comparison over `gf`
followed by the image of the source composition comparison. -/
theorem Reindex.mapIso.specifiedComp.hom
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (gf : W ⟶ U)
    (hgf : g ≫ f = gf) (x : p₁.Fiber U) :
    (Functor.Cleavage.Reindex.specifiedCompIsoApp χ₂ f g gf hgf
      ((F.fiberFunctor U).obj x)).hom ≫
        (χ₂.reindex g).map (Reindex.mapIso F χ₁ χ₂ f x).hom ≫
        (Reindex.mapIso F χ₁ χ₂ g ((χ₁.reindex f).obj x)).hom =
      (Reindex.mapIso F χ₁ χ₂ gf x).hom ≫
        (F.fiberFunctor W).map
          (Functor.Cleavage.Reindex.specifiedCompIsoApp χ₁ f g gf hgf x).hom := sorry
/- Proof strategy: forget to the target total category and postcompose with the chosen cartesian
arrows over `g` and `f`. Use `Reindex.mapIso.hom.fac` and the source and target
`Functor.Cleavage.Reindex.specifiedCompIsoApp.hom.fac` laws; both sides reduce to the image under
`F` of the chosen lift over `gf`. -/

/-- Cancellation form of `Reindex.mapIso.specifiedComp.hom`, suited to the left boundary of
conjugation and `pullHom` calculations. -/
theorem Reindex.mapIso.specifiedComp.boundary
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (gf : W ⟶ U)
    (hgf : g ≫ f = gf) (x : p₁.Fiber U) :
    (Functor.Cleavage.Reindex.specifiedCompIsoApp χ₂ f g gf hgf
      ((F.fiberFunctor U).obj x)).hom ≫
        (χ₂.reindex g).map (Reindex.mapIso F χ₁ χ₂ f x).hom =
      (Reindex.mapIso F χ₁ χ₂ gf x).hom ≫
        (F.fiberFunctor W).map
          (Functor.Cleavage.Reindex.specifiedCompIsoApp χ₁ f g gf hgf x).hom ≫
        (Reindex.mapIso F χ₁ χ₂ g ((χ₁.reindex f).obj x)).inv := sorry
/- Proof strategy: postcompose `Reindex.mapIso.specifiedComp.hom F χ₁ χ₂ f g gf hgf x` with
the inverse comparison over `g`, reassociate, and cancel its hom-inverse pair. -/

/-- Inverse form of the composition coherence for the reindexing comparison of a cartesian
based functor. -/
theorem Reindex.mapIso.specifiedComp.inv
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (gf : W ⟶ U)
    (hgf : g ≫ f = gf) (x : p₁.Fiber U) :
    (Reindex.mapIso F χ₁ χ₂ g ((χ₁.reindex f).obj x)).inv ≫
        (χ₂.reindex g).map (Reindex.mapIso F χ₁ χ₂ f x).inv ≫
        (Functor.Cleavage.Reindex.specifiedCompIsoApp χ₂ f g gf hgf
          ((F.fiberFunctor U).obj x)).inv =
      (F.fiberFunctor W).map
          (Functor.Cleavage.Reindex.specifiedCompIsoApp χ₁ f g gf hgf x).inv ≫
        (Reindex.mapIso F χ₁ χ₂ gf x).inv := sorry
/- Proof strategy: invert `Reindex.mapIso.specifiedComp.hom F χ₁ χ₂ f g gf hgf x`, then cancel
the source and target composition isomorphisms and the three comparison inverse pairs. -/

end CartesianBasedFunctor

end CategoryTheory
