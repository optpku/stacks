/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.EssentialImage
public import ReasLib.AlgebraicGeometry.FormalDeformation.Smooth.SmallExtension
public import ReasLib.CategoryTheory.Cofibered.Comparison

/-!
# Smoothness via essential surjectivity of the mixed fibre comparison

A morphism of categories cofibered in groupoids is smooth if and only if the
comparison functor into the fibrewise categorical pullback is essentially
surjective along surjections, equivalently along small extensions.
-/

@[expose] public section

open CategoryTheory
open ArtinianLocalAlgCat (IsSmallExtension)
open scoped BasedFunctor

universe u v w v' w'

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.BasedFunctor

/-- A morphism `φ : X ⥤ᵇ Y` of categories cofibered in groupoids over
`ArtinianLocalAlgCat Λ k` is smooth if and only if, for every surjection `f : B ⟶ A`
and every choice of pushforward cleavages `χX`, `χY`, the induced comparison
`pushforwardComparison φ χX χY f` into
`(φ.fiberFunctor A) ⊡ (pushforwardFiberFunctor Y.p χY f)` is essentially
surjective. -/
theorem isSmooth_iff_pushforwardComparison_essSurj
    {X : BasedCategory.{v, w} (ArtinianLocalAlgCat Λ k)}
    {Y : BasedCategory.{v', w'} (ArtinianLocalAlgCat Λ k)}
    [Functor.IsFibered.InGroupoids X.p.op] [Functor.IsFibered.InGroupoids Y.p.op]
    (φ : X ⥤ᵇ Y) :
    IsSmooth φ ↔
      ∀ {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A),
        Function.Surjective f.hom →
        ∀ (χX : X.p.op.Cleavage) (χY : Y.p.op.Cleavage),
          (pushforwardComparison φ χX χY f).EssSurj := sorry

/-- Smoothness is equivalent to essential surjectivity of `pushforwardComparison` along
every small extension. -/
theorem isSmooth_iff_pushforwardComparison_essSurj_isSmallExtension
    {X : BasedCategory.{v, w} (ArtinianLocalAlgCat Λ k)}
    {Y : BasedCategory.{v', w'} (ArtinianLocalAlgCat Λ k)}
    [Functor.IsFibered.InGroupoids X.p.op] [Functor.IsFibered.InGroupoids Y.p.op]
    (φ : X ⥤ᵇ Y) :
    IsSmooth φ ↔
      ∀ {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) [IsSmallExtension f]
        (χX : X.p.op.Cleavage) (χY : Y.p.op.Cleavage),
          (pushforwardComparison φ χX χY f).EssSurj := sorry

end CategoryTheory.BasedFunctor
