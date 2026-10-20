module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalDeformation.RimSchlessinger.Associated

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

/- Lemma 90.16.7: if `p : F ⥤ ArtinianLocalAlgCat Λ k` is cofibered in groupoids
and satisfies (RS), then the following are equivalent: the associated functor of
isomorphism classes satisfies (RS); for every cospan `f1 : A1 ⟶ A`, `f2 : A2 ⟶ A`
with `f2` surjective, the induced map on isomorphism classes of the 2-fibre product
of fibres is injective; `fiberAutHom p f φ` is surjective for every cocartesian lift
over a surjection; and the same automorphism map is surjective along every small
extension. -/
@[stacks 06J8] #check (CategoryTheory.Functor.hasRimSchlessinger_isoClass_tfae :
    ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p]
      (χ : p.op.Cleavage),
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
          IsSmallExtension f → Function.Surjective (fiberAutHom p f φ)])
