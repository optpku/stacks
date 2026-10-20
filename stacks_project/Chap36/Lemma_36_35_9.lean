module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Limit.QcqsAffine.BaseChange.RelativePerfect.Colimit

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

/- Lemma 36.35.9: In Situation 36.35.7 the category of `S`-perfect objects of
`D(𝒪_X)` is the colimit of the categories of `Sᵢ`-perfect objects of `D(𝒪_{Xᵢ})`. -/
@[stacks 0DI8] #check
  (AlgebraicGeometry.Scheme.Limit.QcqsAffineLimit.isPerfectOverCategoryColimit :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {D : OrderDual I ⥤ Scheme.{u}}
      [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
      [∀ {i i' : I} (h : i ≤ i'), IsAffineHom (D.map (homOfLE h))]
      (s : Scheme.Limit.QcqsAffineLimit D) (X₀ : Scheme.{u})
      (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
      [∀ U : TopologicalSpace.Opens
        (RingedSpace.Hom.inverseImageBase (s.limitRelative x₀).toShHom).carrier,
        DerivedCategory.DerivedTensor.Right.Has
          (C := RingedSpace.Modules
            ((RingedSpace.Hom.inverseImageBase (s.limitRelative x₀).toShHom).restrict
              U.isOpenEmbedding))]
      [∀ j : (Over (OrderDual.toDual s.base))ᵒᵖ,
        ∀ U : TopologicalSpace.Opens
          (RingedSpace.Hom.inverseImageBase (s.stageRelative x₀ j).toShHom).carrier,
        DerivedCategory.DerivedTensor.Right.Has
          (C := RingedSpace.Modules
            ((RingedSpace.Hom.inverseImageBase (s.stageRelative x₀ j).toShHom).restrict
              U.isOpenEmbedding))]
      [Flat x₀] [Scheme.Hom.FinitePresentation x₀],
      s.IsPerfectOverCategoryColimit x₀)
