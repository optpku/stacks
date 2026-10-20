/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pushforward.Adjunction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Tensor
public import Mathlib.CategoryTheory.Triangulated.Functor

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.DerivedCategory CategoryTheory.MonoidalCategory ComplexShape ObjectProperty
open CategoryTheory.Pretriangulated

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}}

variable {X Y : AlgebraicSpace S} (f : X ⟶ Y)
variable [QuasiCompact f] [QuasiSeparated f]

/-- Pullback comparison `Lf^*(K ⊗^L L) ⟶ Lf^*K ⊗^L Lf^*L` on complexes with quasi-coherent
cohomology. -/
noncomputable def pullbackTensorComparison (K L : DerivedQCoh Y) :
    (pullback f).obj (tensorObj K L) ⟶
      tensorObj ((pullback f).obj K) ((pullback f).obj L) :=
  ObjectProperty.homMk <|
    ((pullback.cellModelInclusionIso f).app (tensorObj K L)).hom ≫
      (ModuleDerived.pullback f).map (tensorObjIsoBifunctor K L).hom ≫
        moduleDerivedPullbackTensorComparison f K.obj L.obj ≫
          (DerivedTensor.Bifunctor.functor (C := Modules X)).map
              (Prod.mkHom
                ((pullback.cellModelInclusionIso f).inv.app K)
                ((pullback.cellModelInclusionIso f).inv.app L)) ≫
            (tensorObjIsoBifunctor ((pullback f).obj K) ((pullback f).obj L)).inv

/-- The underlying morphism of `pullbackTensorComparison` is the ambient derived comparison,
transported along the quasi-coherent inclusions and the fixed-right/two-variable tensor
identifications. -/
theorem pullbackTensorComparison_eq (K L : DerivedQCoh Y) :
    (pullbackTensorComparison f K L).hom =
      ((pullback.cellModelInclusionIso f).app (tensorObj K L)).hom ≫
        (ModuleDerived.pullback f).map (tensorObjIsoBifunctor K L).hom ≫
          moduleDerivedPullbackTensorComparison f K.obj L.obj ≫
            (DerivedTensor.Bifunctor.functor (C := Modules X)).map
                (Prod.mkHom
                  ((pullback.cellModelInclusionIso f).inv.app K)
                  ((pullback.cellModelInclusionIso f).inv.app L)) ≫
              (tensorObjIsoBifunctor ((pullback f).obj K) ((pullback f).obj L)).inv :=
  sorry

/-- Canonical projection-formula mate `K ⊗^L Rf_*E ⟶ Rf_*(Lf^*K ⊗^L E)`. -/
noncomputable def projectionFormulaMate (K : DerivedQCoh Y) (E : DerivedQCoh X) :
    tensorObj K ((pushforwardCohomologyIn f).obj E) ⟶
      (pushforwardCohomologyIn f).obj (tensorObj ((pullback f).obj K) E) :=
  (pullbackPushforwardCohomologyAdjunction f).homEquiv _ _
    (pullbackTensorComparison f K ((pushforwardCohomologyIn f).obj E) ≫
      tensorMapRight ((pullback f).obj K)
        ((pullbackPushforwardCohomologyAdjunction f).counit.app E))

/-- Transposing `projectionFormulaMate` recovers the pullback tensor comparison followed by the
left-tensor of the counit. -/
theorem projectionFormulaMate_spec (K : DerivedQCoh Y) (E : DerivedQCoh X) :
    ((pullbackPushforwardCohomologyAdjunction f).homEquiv _ _).symm
        (projectionFormulaMate f K E) =
      pullbackTensorComparison f K ((pushforwardCohomologyIn f).obj E) ≫
        tensorMapRight ((pullback f).obj K)
          ((pullbackPushforwardCohomologyAdjunction f).counit.app E) :=
  sorry

/-- The projection-formula mate is an isomorphism. -/
instance isIso_projectionFormulaMate (K : DerivedQCoh Y) (E : DerivedQCoh X) :
    IsIso (projectionFormulaMate f K E) :=
  sorry

/-- Canonical projection-formula isomorphism
`Rf_*(Lf^*K ⊗^L E) ≅ K ⊗^L Rf_*E`. -/
noncomputable def projectionFormulaIso (K : DerivedQCoh Y) (E : DerivedQCoh X) :
    (pushforwardCohomologyIn f).obj (tensorObj ((pullback f).obj K) E) ≅
      tensorObj K ((pushforwardCohomologyIn f).obj E) :=
  (asIso (projectionFormulaMate f K E)).symm

/-- The forward map of `projectionFormulaIso` is the inverse of the projection-formula mate. -/
theorem projectionFormulaIso_hom (K : DerivedQCoh Y) (E : DerivedQCoh X) :
    (projectionFormulaIso f K E).hom =
      (asIso (projectionFormulaMate f K E)).inv :=
  sorry

/-- Tensor the counit `Rf_* a(L) ⟶ L` with `K` in `DerivedQCoh Y`. -/
noncomputable def tensorCounitMap
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (K L : DerivedQCoh Y) :
    tensorObj K ((pushforwardCohomologyIn f).obj (a.obj L)) ⟶ tensorObj K L :=
  tensorMapRight K (aAdjunction.counit.app L)

/-- The underlying morphism of `tensorCounitMap` is the left-tensor of the adjunction counit. -/
theorem tensorCounitMap_spec
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (K L : DerivedQCoh Y) :
    tensorCounitMap f a aAdjunction K L =
      tensorMapRight K (aAdjunction.counit.app L) :=
  sorry

/-- Specializing the tensor of the counit to `𝒪_Y` and applying the right unitor on `K`
gives `K ⊗^L Rf_* a(𝒪_Y) ⟶ K`. -/
noncomputable def tensorCounitToUnit
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (K : DerivedQCoh Y) :
    tensorObj K ((pushforwardCohomologyIn f).obj (a.obj (structureSheaf Y))) ⟶ K :=
  tensorCounitMap f a aAdjunction K (structureSheaf Y) ≫ tensorUnitor K

/-- `tensorCounitToUnit` is the counit tensor map followed by the right unitor on `K`. -/
theorem tensorCounitToUnit_spec
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (K : DerivedQCoh Y) :
    tensorCounitToUnit f a aAdjunction K =
      tensorCounitMap f a aAdjunction K (structureSheaf Y) ≫ tensorUnitor K :=
  sorry

/-- The projection-formula and counit map
`Lf^*K ⊗^L a(L) ⟶ a(K ⊗^L L)` for a chosen right adjoint `a` to `Rf_*`. -/
noncomputable def pullbackTensorRightAdjointMap
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (K L : DerivedQCoh Y) :
    tensorObj ((pullback f).obj K) (a.obj L) ⟶ a.obj (tensorObj K L) :=
  aAdjunction.homEquiv _ _
    ((projectionFormulaIso f K (a.obj L)).hom ≫ tensorCounitMap f a aAdjunction K L)

/-- Transposing `pullbackTensorRightAdjointMap` recovers the projection-formula isomorphism
followed by the tensor of the counit. -/
theorem pullbackTensorRightAdjointMap_spec
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (K L : DerivedQCoh Y) :
    (aAdjunction.homEquiv _ _).symm (pullbackTensorRightAdjointMap f a aAdjunction K L) =
      (projectionFormulaIso f K (a.obj L)).hom ≫
        tensorCounitMap f a aAdjunction K L :=
  sorry

/-- The canonical comparison `Lf^*K ⊗^L a(𝒪_Y) ⟶ a(K)` obtained from the projection
formula and the counit of `Rf_* ⊣ a`. -/
noncomputable def pullbackTensorDualityMap
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (K : DerivedQCoh Y) :
    tensorObj ((pullback f).obj K) (a.obj (structureSheaf Y)) ⟶ a.obj K :=
  aAdjunction.homEquiv _ _
    ((projectionFormulaIso f K (a.obj (structureSheaf Y))).hom ≫
      tensorCounitToUnit f a aAdjunction K)

/-- Transposing `pullbackTensorDualityMap` recovers the projection formula followed by the
counit-to-unit map. -/
theorem pullbackTensorDualityMap_spec
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (K : DerivedQCoh Y) :
    (aAdjunction.homEquiv _ _).symm (pullbackTensorDualityMap f a aAdjunction K) =
      (projectionFormulaIso f K (a.obj (structureSheaf Y))).hom ≫
        tensorCounitToUnit f a aAdjunction K :=
  sorry

/-- The duality comparison is natural in `K`. -/
theorem pullbackTensorDualityMap_naturality
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    {K K' : DerivedQCoh Y} (g : K ⟶ K') :
    (pullback f ⋙ tensorRight (a.obj (structureSheaf Y))).map g ≫
        pullbackTensorDualityMap f a aAdjunction K' =
      pullbackTensorDualityMap f a aAdjunction K ≫ a.map g :=
  sorry

/-- The canonical duality comparisons, packaged as a natural transformation in `K`. -/
noncomputable def pullbackTensorDualityNatTrans
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a) :
    pullback f ⋙ tensorRight (a.obj (structureSheaf Y)) ⟶ a where
  app K := pullbackTensorDualityMap f a aAdjunction K
  naturality _ _ g := pullbackTensorDualityMap_naturality f a aAdjunction g

/-- The component of `pullbackTensorDualityNatTrans` is `pullbackTensorDualityMap`. -/
theorem pullbackTensorDualityNatTrans_app
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (K : DerivedQCoh Y) :
    (pullbackTensorDualityNatTrans f a aAdjunction).app K =
      pullbackTensorDualityMap f a aAdjunction K :=
  sorry

/-- The duality transformation commutes with the canonical shifts and the shift induced
on its target by the supplied adjunction. -/
theorem pullbackTensorDualityNatTrans_commShift
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a) :
    -- Local instance justification (defeq pin): use the shift structure induced by this explicit adjunction; no arbitrary right-adjoint shift is assumed.
    letI := rightAdjointCommShift f a aAdjunction
    NatTrans.CommShift (pullbackTensorDualityNatTrans f a aAdjunction) ℤ :=
  sorry

/-- The canonical duality comparison defines a morphism between the images of a
distinguished triangle under the tensor-pullback functor and the supplied right adjoint. -/
noncomputable def pullbackTensorDuality_distinguishedTriangle
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (T : Triangle (DerivedQCoh Y))
    (distinguished : T ∈ distTriang (DerivedQCoh Y)) :
    -- Local instance justification (defeq pin): use the shift structure induced by this explicit adjunction; no arbitrary right-adjoint shift is assumed.
    letI := rightAdjointCommShift f a aAdjunction
    TriangleMorphism
      ((pullback f ⋙ tensorRight (a.obj (structureSheaf Y))).mapTriangle.obj T)
      (a.mapTriangle.obj T) := by
  -- Local instance justification (defeq pin): use the shift structure induced by this explicit adjunction; no arbitrary right-adjoint shift is assumed.
  letI := rightAdjointCommShift f a aAdjunction
  exact {
    hom₁ := pullbackTensorDualityMap f a aAdjunction T.obj₁
    hom₂ := pullbackTensorDualityMap f a aAdjunction T.obj₂
    hom₃ := pullbackTensorDualityMap f a aAdjunction T.obj₃
    comm₁ := pullbackTensorDualityMap_naturality f a aAdjunction T.mor₁
    comm₂ := pullbackTensorDualityMap_naturality f a aAdjunction T.mor₂
    comm₃ := by
      have compatibility := congr_app
        ((pullbackTensorDualityNatTrans_commShift f a aAdjunction).shift_comm (1 : ℤ)) T.obj₁
      change
        ((pullback f ⋙ tensorRight (a.obj (structureSheaf Y))).map T.mor₃ ≫
            (Functor.commShiftIso (pullback f ⋙ tensorRight (a.obj (structureSheaf Y)))
              (1 : ℤ)).hom.app T.obj₁) ≫
            (shiftFunctor (DerivedQCoh X) (1 : ℤ)).map
              (pullbackTensorDualityMap f a aAdjunction T.obj₁) =
          pullbackTensorDualityMap f a aAdjunction T.obj₃ ≫
            a.map T.mor₃ ≫ (a.commShiftIso (1 : ℤ)).hom.app T.obj₁
      change
        (Functor.commShiftIso (pullback f ⋙ tensorRight (a.obj (structureSheaf Y)))
            (1 : ℤ)).hom.app T.obj₁ ≫
            (shiftFunctor (DerivedQCoh X) (1 : ℤ)).map
              (pullbackTensorDualityMap f a aAdjunction T.obj₁) =
          pullbackTensorDualityMap f a aAdjunction (T.obj₁⟦(1 : ℤ)⟧) ≫
            (a.commShiftIso (1 : ℤ)).hom.app T.obj₁ at compatibility
      refine Eq.trans (Category.assoc _ _ _) ?_
      refine Eq.trans (congrArg
        (fun g ↦ (pullback f ⋙ tensorRight (a.obj (structureSheaf Y))).map T.mor₃ ≫ g)
        compatibility) ?_
      refine Eq.trans (Category.assoc _ _ _).symm ?_
      refine Eq.trans (congrArg (fun g ↦ g ≫ (a.commShiftIso (1 : ℤ)).hom.app T.obj₁)
        (pullbackTensorDualityMap_naturality f a aAdjunction T.mor₃)) ?_
      exact Category.assoc _ _ _ }

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
