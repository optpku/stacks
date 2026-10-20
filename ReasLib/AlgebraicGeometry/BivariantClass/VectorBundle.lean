/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Composition
public import ReasLib.AlgebraicGeometry.BivariantClass.FlatPullback
public import ReasLib.AlgebraicGeometry.ChowGroup.FlatPullback.VectorBundle
public import ReasLib.AlgebraicGeometry.Scheme.VectorBundle.FiniteLocallyFree

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

/-- Composition with vector-bundle flat pullback sends the zero class to zero. -/
theorem vectorBundleComposition_map_zero
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (E : X.left.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra E))
    [Scheme.IsRelativeSpectrumOver P] :
    ((neg_add_cancel (r : ℤ)) ▸
      @comp S _ delta _ _ _ _ (Scheme.AssociatedVectorBundle.locallyOfFiniteTypeComp X E P) _ _
        (Over.homMk (Scheme.associatedVectorBundleπ E P) :
        Over.mk (Scheme.associatedVectorBundleπ E P ≫ X.hom) ⟶ X) f (-(r : ℤ)) (r : ℤ)
        (@flatPullback S _ delta _ _ _ (Scheme.AssociatedVectorBundle.locallyOfFiniteTypeComp X E P) _
          (Over.homMk (Scheme.associatedVectorBundleπ E P) :
        Over.mk (Scheme.associatedVectorBundleπ E P ≫ X.hom) ⟶ X) r
          (Scheme.AssociatedVectorBundle.overHomFlat X E P)
          (Scheme.AssociatedVectorBundle.overHomRelativeDimension X E r P)) (pointwiseZero delta f (r : ℤ))) =
      @pointwiseZero S _ delta _ _ _ (Scheme.AssociatedVectorBundle.locallyOfFiniteTypeComp X E P) _ ((Over.homMk (Scheme.associatedVectorBundleπ E P) :
        Over.mk (Scheme.associatedVectorBundleπ E P ≫ X.hom) ⟶ X) ≫ f) 0 := sorry

/-- Composition with vector-bundle flat pullback preserves pointwise addition. -/
theorem vectorBundleComposition_map_add
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (E : X.left.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra E))
    [Scheme.IsRelativeSpectrumOver P] (c d : BivariantClass delta f (r : ℤ)) :
    ((neg_add_cancel (r : ℤ)) ▸
      @comp S _ delta _ _ _ _ (Scheme.AssociatedVectorBundle.locallyOfFiniteTypeComp X E P) _ _
        (Over.homMk (Scheme.associatedVectorBundleπ E P) :
        Over.mk (Scheme.associatedVectorBundleπ E P ≫ X.hom) ⟶ X) f (-(r : ℤ)) (r : ℤ)
        (@flatPullback S _ delta _ _ _ (Scheme.AssociatedVectorBundle.locallyOfFiniteTypeComp X E P) _
          (Over.homMk (Scheme.associatedVectorBundleπ E P) :
        Over.mk (Scheme.associatedVectorBundleπ E P ≫ X.hom) ⟶ X) r
          (Scheme.AssociatedVectorBundle.overHomFlat X E P)
          (Scheme.AssociatedVectorBundle.overHomRelativeDimension X E r P)) (pointwiseAdd delta f (r : ℤ) c d)) =
      @pointwiseAdd S _ delta _ _ _ (Scheme.AssociatedVectorBundle.locallyOfFiniteTypeComp X E P) _ ((Over.homMk (Scheme.associatedVectorBundleπ E P) :
        Over.mk (Scheme.associatedVectorBundleπ E P ≫ X.hom) ⟶ X) ≫ f) 0
        ((neg_add_cancel (r : ℤ)) ▸
      @comp S _ delta _ _ _ _ (Scheme.AssociatedVectorBundle.locallyOfFiniteTypeComp X E P) _ _
        (Over.homMk (Scheme.associatedVectorBundleπ E P) :
        Over.mk (Scheme.associatedVectorBundleπ E P ≫ X.hom) ⟶ X) f (-(r : ℤ)) (r : ℤ)
        (@flatPullback S _ delta _ _ _ (Scheme.AssociatedVectorBundle.locallyOfFiniteTypeComp X E P) _
          (Over.homMk (Scheme.associatedVectorBundleπ E P) :
        Over.mk (Scheme.associatedVectorBundleπ E P ≫ X.hom) ⟶ X) r
          (Scheme.AssociatedVectorBundle.overHomFlat X E P)
          (Scheme.AssociatedVectorBundle.overHomRelativeDimension X E r P)) c) ((neg_add_cancel (r : ℤ)) ▸
      @comp S _ delta _ _ _ _ (Scheme.AssociatedVectorBundle.locallyOfFiniteTypeComp X E P) _ _
        (Over.homMk (Scheme.associatedVectorBundleπ E P) :
        Over.mk (Scheme.associatedVectorBundleπ E P ≫ X.hom) ⟶ X) f (-(r : ℤ)) (r : ℤ)
        (@flatPullback S _ delta _ _ _ (Scheme.AssociatedVectorBundle.locallyOfFiniteTypeComp X E P) _
          (Over.homMk (Scheme.associatedVectorBundleπ E P) :
        Over.mk (Scheme.associatedVectorBundleπ E P ≫ X.hom) ⟶ X) r
          (Scheme.AssociatedVectorBundle.overHomFlat X E P)
          (Scheme.AssociatedVectorBundle.overHomRelativeDimension X E r P)) d) := sorry

/-- The additive map given by composition with flat pullback along a rank-`r` vector bundle. -/
noncomputable def vectorBundleComposition
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (E : X.left.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra E))
    [Scheme.IsRelativeSpectrumOver P] :
    @AddMonoidHom (BivariantClass delta f (r : ℤ))
      (@BivariantClass S _ delta _ _ _ (Scheme.AssociatedVectorBundle.locallyOfFiniteTypeComp X E P) _ ((Over.homMk (Scheme.associatedVectorBundleπ E P) :
        Over.mk (Scheme.associatedVectorBundleπ E P ≫ X.hom) ⟶ X) ≫ f) 0)
      (pointwiseAddCommGroup delta f (r : ℤ)).toAddZero
      (@pointwiseAddCommGroup S _ delta _ _ _ (Scheme.AssociatedVectorBundle.locallyOfFiniteTypeComp X E P) _
        ((Over.homMk (Scheme.associatedVectorBundleπ E P) :
        Over.mk (Scheme.associatedVectorBundleπ E P ≫ X.hom) ⟶ X) ≫ f) 0).toAddZero :=
  @AddMonoidHom.mk _ _ (pointwiseAddCommGroup delta f (r : ℤ)).toAddZero (@pointwiseAddCommGroup S _ delta _ _ _ (Scheme.AssociatedVectorBundle.locallyOfFiniteTypeComp X E P) _
        ((Over.homMk (Scheme.associatedVectorBundleπ E P) :
        Over.mk (Scheme.associatedVectorBundleπ E P ≫ X.hom) ⟶ X) ≫ f) 0).toAddZero
    (@ZeroHom.mk _ _ (pointwiseAddCommGroup delta f (r : ℤ)).toZero (@pointwiseAddCommGroup S _ delta _ _ _ (Scheme.AssociatedVectorBundle.locallyOfFiniteTypeComp X E P) _
        ((Over.homMk (Scheme.associatedVectorBundleπ E P) :
        Over.mk (Scheme.associatedVectorBundleπ E P ≫ X.hom) ⟶ X) ≫ f) 0).toZero (fun c ↦ ((neg_add_cancel (r : ℤ)) ▸
      @comp S _ delta _ _ _ _ (Scheme.AssociatedVectorBundle.locallyOfFiniteTypeComp X E P) _ _
        (Over.homMk (Scheme.associatedVectorBundleπ E P) :
        Over.mk (Scheme.associatedVectorBundleπ E P ≫ X.hom) ⟶ X) f (-(r : ℤ)) (r : ℤ)
        (@flatPullback S _ delta _ _ _ (Scheme.AssociatedVectorBundle.locallyOfFiniteTypeComp X E P) _
          (Over.homMk (Scheme.associatedVectorBundleπ E P) :
        Over.mk (Scheme.associatedVectorBundleπ E P ≫ X.hom) ⟶ X) r
          (Scheme.AssociatedVectorBundle.overHomFlat X E P)
          (Scheme.AssociatedVectorBundle.overHomRelativeDimension X E r P)) c)
  ) (vectorBundleComposition_map_zero delta f E r P))
    (vectorBundleComposition_map_add delta f E r P)

/-- Composition with vector-bundle flat pullback is bijective on bivariant classes. -/
theorem vectorBundleComposition_bijective
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (E : X.left.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra E))
    [Scheme.IsRelativeSpectrumOver P] :
    Function.Bijective (vectorBundleComposition delta f E r P) := sorry

end AlgebraicGeometry.BivariantClass
