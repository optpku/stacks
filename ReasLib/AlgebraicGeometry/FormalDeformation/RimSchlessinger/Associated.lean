/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.FormalDeformation.RimSchlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger.Associated
public import ReasLib.AlgebraicGeometry.FormalDeformation.SmallExtension
public import ReasLib.CategoryTheory.Fibered.InfinitesimalAutomorphisms
public import ReasLib.CategoryTheory.Cofibered.IsoClassComparison

/-!
# Rim-Schlessinger for the associated functor of isomorphism classes

For a category cofibered in groupoids satisfying (RS), the associated functor
satisfies (RS) exactly when the two-fibre-product comparison is injective, or
equivalently when automorphisms lift along surjections or small extensions.

Every total-category morphism in a cofibered groupoid is cocartesian: its opposite
is Cartesian by the groupoid-fibration property, and reversing its universal
property gives the cocartesian universal property. For a morphism lifting a
specified base arrow, the lift identifies that arrow with its image under the
projection. Thus the cocartesian binders below are well-posedness certificates
for the induced automorphism homomorphisms, not additional restrictions on the
morphisms being quantified over.
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

/-- For a category cofibered in groupoids satisfying (RS), the following are
equivalent: its associated functor of isomorphism classes satisfies (RS); the
two-fibre-product comparison is injective along cospans with surjective second
leg; automorphisms lift along every surjection; and automorphisms lift along
every small extension. -/
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

/-- Under (RS), the associated functor of isomorphism classes satisfies (RS) if
and only if the two-fibre-product comparison is injective along every cospan
with surjective second leg. -/
theorem hasRimSchlessinger_isoClass_iff_fiberProductIsoClass_injective
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p]
    (χ : p.op.Cleavage) :
    HasRimSchlessinger (CategoryOfElements.π (isoClassFunctor p)) ↔
      ∀ {A A1 A2 : ArtinianLocalAlgCat Λ k} (f1 : A1 ⟶ A) (f2 : A2 ⟶ A),
        Function.Surjective f2.hom →
          Function.Injective (fiberProductIsoClassComparison p χ f1 f2) :=
  sorry

/-- Under (RS), injectivity of the two-fibre-product comparison along surjections
is equivalent to surjectivity of the induced fibre automorphism homomorphism
along every lifted surjection. -/
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

/-- Under (RS), surjectivity of the induced fibre automorphism homomorphism
along all surjections is equivalent to surjectivity along all small extensions. -/
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
