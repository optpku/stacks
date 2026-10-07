module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap90.Definition_90_16_8_RimSchlessinger
public import stacks_project.Chap90.Definition_90_19_1_InfinitesimalAut
public import stacks_project.Chap90.Definition_90_3_2_SmallExtension
public import stacks_project.Chap90.Lemma_90_10_5_Associated
public import stacks_project.Chap90.Lemma_90_16_7_Comparison

/-!
# Rim-Schlessinger for the associated functor of isomorphism classes

If a category cofibered in groupoids over `ArtinianLocalAlgCat Λ k` satisfies (RS),
then (RS) for the associated functor of isomorphism classes is equivalent to
injectivity of the iso-class comparison of fibre 2-fibre products, and to
surjectivity of fibre automorphism maps along surjections or small extensions.
-/

@[expose] public section

open CategoryTheory Functor Limits
open ArtinianLocalAlgCat (IsSmallExtension)
open Fiber
open scoped CategoricalPullback

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

/-- The Rim-Schlessinger condition includes being cofibered in groupoids. -/
instance HasRimSchlessinger.toIsFiberedInGroupoids
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p] :
    IsFibered.InGroupoids p.op :=
  HasRimSchlessinger.isCofiberedInGroupoids

/-- Lemma 90.16.7: if `p : F ⥤ ArtinianLocalAlgCat Λ k` is cofibered in groupoids
and satisfies (RS), then the following are equivalent: the associated functor of
isomorphism classes satisfies (RS); for every cospan `f1 : A1 ⟶ A`, `f2 : A2 ⟶ A`
with `f2` surjective, the induced map on isomorphism classes of the 2-fibre product
of fibres is injective; `fiberAutHom p f φ` is surjective for every cocartesian lift
over a surjection; and the same automorphism map is surjective along every small
extension. -/
@[stacks 06J8]
theorem hasRimSchlessinger_isoClass_tfae
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p]
    (χ : p.op.Cleavage) :
    List.TFAE
      [HasRimSchlessinger (CategoryOfElements.π (isoClassFunctor p)),
        ∀ {A A1 A2 : ArtinianLocalAlgCat Λ k} (f1 : A1 ⟶ A) (f2 : A2 ⟶ A),
          Function.Surjective f2.hom →
            Function.Injective (fiberProductIsoClassComparison p χ f1 f2),
        ∀ {A' A : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A)
          {x' : p.Fiber A'} {x : p.Fiber A}
          (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x)
          [p.IsHomLift f φ] [p.IsCocartesian f φ],
          Function.Surjective f.hom → Function.Surjective (fiberAutHom p f φ),
        ∀ {A' A : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A)
          {x' : p.Fiber A'} {x : p.Fiber A}
          (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x)
          [p.IsHomLift f φ] [p.IsCocartesian f φ],
          IsSmallExtension f → Function.Surjective (fiberAutHom p f φ)] :=
  sorry

/-- Under (RS), the associated functor of isomorphism classes satisfies (RS) if and
only if the fibre 2-fibre product iso-class comparison is injective along every
cospan with surjective second leg. -/
theorem hasRimSchlessinger_isoClass_iff_fiberProductIsoClass_injective
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p]
    (χ : p.op.Cleavage) :
    HasRimSchlessinger (CategoryOfElements.π (isoClassFunctor p)) ↔
      ∀ {A A1 A2 : ArtinianLocalAlgCat Λ k} (f1 : A1 ⟶ A) (f2 : A2 ⟶ A),
        Function.Surjective f2.hom →
          Function.Injective (fiberProductIsoClassComparison p χ f1 f2) :=
  sorry

/-- Under (RS), injectivity of the fibre 2-fibre product iso-class comparison along
surjections is equivalent to surjectivity of `fiberAutHom` along every cocartesian
lift over a surjection. -/
theorem fiberProductIsoClass_injective_iff_fiberAutHom_surjective
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p]
    (χ : p.op.Cleavage) :
    (∀ {A A1 A2 : ArtinianLocalAlgCat Λ k} (f1 : A1 ⟶ A) (f2 : A2 ⟶ A),
        Function.Surjective f2.hom →
          Function.Injective (fiberProductIsoClassComparison p χ f1 f2)) ↔
      ∀ {A' A : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A)
        {x' : p.Fiber A'} {x : p.Fiber A}
        (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x)
        [p.IsHomLift f φ] [p.IsCocartesian f φ],
        Function.Surjective f.hom → Function.Surjective (fiberAutHom p f φ) :=
  sorry

/-- Under (RS), surjectivity of `fiberAutHom` along surjections is equivalent to
surjectivity of `fiberAutHom` along small extensions. -/
theorem fiberAutHom_surjective_iff_isSmallExtension
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p] :
    (∀ {A' A : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A)
        {x' : p.Fiber A'} {x : p.Fiber A}
        (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x)
        [p.IsHomLift f φ] [p.IsCocartesian f φ],
        Function.Surjective f.hom → Function.Surjective (fiberAutHom p f φ)) ↔
      ∀ {A' A : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A)
        {x' : p.Fiber A'} {x : p.Fiber A}
        (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x)
        [p.IsHomLift f φ] [p.IsCocartesian f φ],
        IsSmallExtension f → Function.Surjective (fiberAutHom p f φ) :=
  sorry

end CategoryTheory.Functor
