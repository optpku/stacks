module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Localization.Prod
public import Mathlib.CategoryTheory.Triangulated.Basic
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Cochain
public import stacks_project.Chap86.«86_7_0_1_Pullback»

/-!
# Projection formula and the duality comparison `Lf^*K ⊗^L a(𝒪_Y) ⟶ a(K)`

Given a quasi-compact quasi-separated morphism of algebraic spaces and a chosen right adjoint
`a` of `Rf_*` on `DerivedQCoh`, the canonical derived-tensor projection formula and the counit
of `Rf_* ⊣ a` produce the comparison morphism `Lf^*K ⊗^L a(𝒪_Y) ⟶ a(K)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.DerivedCategory CategoryTheory.Functor CategoryTheory.Pretriangulated
open CategoryTheory.MonoidalCategory ComplexShape ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}}
variable {X Y : AlgebraicSpace S} (f : X ⟶ Y)
variable [QuasiCompact f] [QuasiSeparated f]

/-- Functoriality of `tensorObj` in both factors, via the two-variable derived tensor. -/
noncomputable def tensorMap {Z : AlgebraicSpace S} {K K' L L' : DerivedQCoh Z}
    (g : K ⟶ K') (h : L ⟶ L') :
    tensorObj K L ⟶ tensorObj K' L' :=
  ObjectProperty.homMk <|
    (tensorObjIsoBifunctor K L).hom ≫
      (DerivedTensor.Bifunctor.functor (C := Modules Z)).map (Prod.mkHom g.hom h.hom) ≫
        (tensorObjIsoBifunctor K' L').inv

/-- The underlying morphism of `tensorMap` is the two-variable derived tensor of the two
components. -/
theorem tensorMap_eq {Z : AlgebraicSpace S} {K K' L L' : DerivedQCoh Z}
    (g : K ⟶ K') (h : L ⟶ L') :
    (tensorMap g h).hom =
      (tensorObjIsoBifunctor K L).hom ≫
        (DerivedTensor.Bifunctor.functor (C := Modules Z)).map (Prod.mkHom g.hom h.hom) ≫
          (tensorObjIsoBifunctor K' L').inv :=
  sorry

/-- The cochain-level counit `Lf^*(Q K) ⟶ Q(f^* K)` of derived module pullback. -/
noncomputable def modulePullbackDerived_cochainCounit
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (K : CochainComplex (Modules Y) ℤ) :
    (modulePullbackDerived f).obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj
        (((Modules.pullback f).mapHomologicalComplex (up ℤ)).obj K) :=
  (modulePullbackDerived f).map
      ((DerivedCategory.quotientCompQhIso (Modules Y)).inv.app K) ≫
    ((modulePullbackToDerived f).totalLeftDerivedCounit
        (DerivedCategory.Qh : HomotopyCategory (Modules Y) (up ℤ) ⥤ ModuleDerived Y)
        (ModuleQis Y)).app
      ((HomotopyCategory.quotient (Modules Y) (up ℤ)).obj K) ≫
    (Homotopy.cochainIso (Modules.pullback f)).hom.app K

/-- `modulePullbackDerived_cochainCounit` is the total left-derived counit transported along
`quotientCompQhIso` and the homotopy-to-cochain comparison. -/
theorem modulePullbackDerived_cochainCounit_eq
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (K : CochainComplex (Modules Y) ℤ) :
    modulePullbackDerived_cochainCounit f K =
      (modulePullbackDerived f).map
          ((DerivedCategory.quotientCompQhIso (Modules Y)).inv.app K) ≫
        ((modulePullbackToDerived f).totalLeftDerivedCounit
            (DerivedCategory.Qh : HomotopyCategory (Modules Y) (up ℤ) ⥤ ModuleDerived Y)
            (ModuleQis Y)).app
          ((HomotopyCategory.quotient (Modules Y) (up ℤ)).obj K) ≫
        (Homotopy.cochainIso (Modules.pullback f)).hom.app K :=
  sorry

/-- Underived cochain-level source `Q(f^*K ⊗ f^*L)` of the derived pullback tensor comparison. -/
noncomputable abbrev modulePullbackCochainTensorSource
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    CochainComplex (Modules Y) ℤ × CochainComplex (Modules Y) ℤ ⥤ ModuleDerived X :=
  ((Modules.pullback f).mapHomologicalComplex (up ℤ)).prod
      ((Modules.pullback f).mapHomologicalComplex (up ℤ)) ⋙
    tensor (CochainComplex (Modules X) ℤ) ⋙
    (DerivedCategory.Q : CochainComplex (Modules X) ℤ ⥤ ModuleDerived X)

/-- Derived functor `Lf^*(A ⊗^L B)` in two variables. -/
noncomputable abbrev moduleDerivedTensorThenPullback
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ModuleDerived Y × ModuleDerived Y ⥤ ModuleDerived X :=
  DerivedTensor.Bifunctor.functor (C := Modules Y) ⋙ modulePullbackDerived f

/-- Derived functor `Lf^*A ⊗^L Lf^*B` in two variables. -/
noncomputable abbrev moduleDerivedPullbackThenTensor
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ModuleDerived Y × ModuleDerived Y ⥤ ModuleDerived X :=
  (modulePullbackDerived f).prod (modulePullbackDerived f) ⋙
    DerivedTensor.Bifunctor.functor (C := Modules X)

/-- Counit of `Lf^*A ⊗^L Lf^*B` against the cochain-level source `Q(f^*K ⊗ f^*L)`. -/
noncomputable def moduleDerivedPullbackThenTensorCounit
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (DerivedCategory.Q : CochainComplex (Modules Y) ℤ ⥤ ModuleDerived Y).prod
        (DerivedCategory.Q : CochainComplex (Modules Y) ℤ ⥤ ModuleDerived Y) ⋙
      moduleDerivedPullbackThenTensor f ⟶
    modulePullbackCochainTensorSource f where
  app KL :=
    (DerivedTensor.Bifunctor.functor (C := Modules X)).map
        (Prod.mkHom
          (modulePullbackDerived_cochainCounit f KL.1)
          (modulePullbackDerived_cochainCounit f KL.2)) ≫
      DerivedTensor.Bifunctor.counitAppOfQ
        (((Modules.pullback f).mapHomologicalComplex (up ℤ)).obj KL.1)
        (((Modules.pullback f).mapHomologicalComplex (up ℤ)).obj KL.2)
  naturality _ _ _ := sorry

/-- The component of `moduleDerivedPullbackThenTensorCounit` is the pair of cochain counits
followed by the two-variable derived-tensor counit. -/
theorem moduleDerivedPullbackThenTensorCounit_app
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (K L : CochainComplex (Modules Y) ℤ) :
    (moduleDerivedPullbackThenTensorCounit f).app (K, L) =
      (DerivedTensor.Bifunctor.functor (C := Modules X)).map
          (Prod.mkHom
            (modulePullbackDerived_cochainCounit f K)
            (modulePullbackDerived_cochainCounit f L)) ≫
        DerivedTensor.Bifunctor.counitAppOfQ
          (((Modules.pullback f).mapHomologicalComplex (up ℤ)).obj K)
          (((Modules.pullback f).mapHomologicalComplex (up ℤ)).obj L) :=
  sorry

/-- Counit of `Lf^*(A ⊗^L B)` against the cochain-level source `Q(f^*K ⊗ f^*L)`. -/
noncomputable def moduleDerivedTensorThenPullbackCounit
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (DerivedCategory.Q : CochainComplex (Modules Y) ℤ ⥤ ModuleDerived Y).prod
        (DerivedCategory.Q : CochainComplex (Modules Y) ℤ ⥤ ModuleDerived Y) ⋙
      moduleDerivedTensorThenPullback f ⟶
    modulePullbackCochainTensorSource f where
  app KL :=
    (modulePullbackDerived f).map (DerivedTensor.Bifunctor.counitAppOfQ KL.1 KL.2) ≫
      modulePullbackDerived_cochainCounit f (KL.1 ⊗ KL.2) ≫
      DerivedCategory.Q.map (modulesPullback_cochainTensorComparison f KL.1 KL.2)
  naturality _ _ _ := sorry

/-- The component of `moduleDerivedTensorThenPullbackCounit` is derived pullback of the tensor
counit, followed by the cochain counit and the cochain-level pullback tensorator. -/
theorem moduleDerivedTensorThenPullbackCounit_app
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (K L : CochainComplex (Modules Y) ℤ) :
    (moduleDerivedTensorThenPullbackCounit f).app (K, L) =
      (modulePullbackDerived f).map (DerivedTensor.Bifunctor.counitAppOfQ K L) ≫
        modulePullbackDerived_cochainCounit f (K ⊗ L) ≫
        DerivedCategory.Q.map (modulesPullback_cochainTensorComparison f K L) :=
  sorry

/-- `Lf^*A ⊗^L Lf^*B` is a left derived functor of the cochain-level source
`Q(f^*K ⊗ f^*L)`. -/
instance moduleDerivedPullbackThenTensor_isLeftDerived
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (moduleDerivedPullbackThenTensor f).IsLeftDerivedFunctor
      (moduleDerivedPullbackThenTensorCounit f)
      ((HomologicalComplex.quasiIso (Modules Y) (up ℤ)).prod
        (HomologicalComplex.quasiIso (Modules Y) (up ℤ))) :=
  sorry

/-- The derived comparison `Lf^*(A ⊗^L B) ⟶ Lf^*A ⊗^L Lf^*B` as a natural transformation. -/
noncomputable def moduleDerivedPullbackTensorComparisonNatTrans
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    moduleDerivedTensorThenPullback f ⟶ moduleDerivedPullbackThenTensor f :=
  (moduleDerivedPullbackThenTensor f).leftDerivedLift
    (moduleDerivedPullbackThenTensorCounit f)
    ((HomologicalComplex.quasiIso (Modules Y) (up ℤ)).prod
      (HomologicalComplex.quasiIso (Modules Y) (up ℤ)))
    (moduleDerivedTensorThenPullback f)
    (moduleDerivedTensorThenPullbackCounit f)

/-- `moduleDerivedPullbackTensorComparisonNatTrans` is the left-derived lift of the
tensor-then-pullback counit against the pullback-then-tensor model. -/
theorem moduleDerivedPullbackTensorComparisonNatTrans_eq
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    moduleDerivedPullbackTensorComparisonNatTrans f =
      (moduleDerivedPullbackThenTensor f).leftDerivedLift
        (moduleDerivedPullbackThenTensorCounit f)
        ((HomologicalComplex.quasiIso (Modules Y) (up ℤ)).prod
          (HomologicalComplex.quasiIso (Modules Y) (up ℤ)))
        (moduleDerivedTensorThenPullback f)
        (moduleDerivedTensorThenPullbackCounit f) :=
  sorry

/-- Ambient derived comparison `Lf^*(A ⊗^L B) ⟶ Lf^*A ⊗^L Lf^*B`. -/
noncomputable def moduleDerivedPullbackTensorComparison
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (A B : ModuleDerived Y) :
    (modulePullbackDerived f).obj
        ((DerivedTensor.Bifunctor.functor (C := Modules Y)).obj (A, B)) ⟶
      (DerivedTensor.Bifunctor.functor (C := Modules X)).obj
        ((modulePullbackDerived f).obj A, (modulePullbackDerived f).obj B) :=
  (moduleDerivedPullbackTensorComparisonNatTrans f).app (A, B)

/-- `moduleDerivedPullbackTensorComparison` is the component of the derived comparison
natural transformation. -/
theorem moduleDerivedPullbackTensorComparison_eq
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (A B : ModuleDerived Y) :
    moduleDerivedPullbackTensorComparison f A B =
      (moduleDerivedPullbackTensorComparisonNatTrans f).app (A, B) :=
  sorry

/-- Pullback comparison `Lf^*(K ⊗^L L) ⟶ Lf^*K ⊗^L Lf^*L` on complexes with quasi-coherent
cohomology. -/
noncomputable def pullbackTensorComparison (K L : DerivedQCoh Y) :
    (pullback f).obj (tensorObj K L) ⟶
      tensorObj ((pullback f).obj K) ((pullback f).obj L) :=
  ObjectProperty.homMk <|
    ((pullback.inclusionIso f).app (tensorObj K L)).hom ≫
      (modulePullbackDerived f).map (tensorObjIsoBifunctor K L).hom ≫
        moduleDerivedPullbackTensorComparison f K.obj L.obj ≫
          (DerivedTensor.Bifunctor.functor (C := Modules X)).map
              (Prod.mkHom
                ((pullback.inclusionIso f).inv.app K)
                ((pullback.inclusionIso f).inv.app L)) ≫
            (tensorObjIsoBifunctor ((pullback f).obj K) ((pullback f).obj L)).inv

/-- The underlying morphism of `pullbackTensorComparison` is the ambient derived comparison,
transported along the quasi-coherent inclusions and the fixed-right/two-variable tensor
identifications. -/
theorem pullbackTensorComparison_eq (K L : DerivedQCoh Y) :
    (pullbackTensorComparison f K L).hom =
      ((pullback.inclusionIso f).app (tensorObj K L)).hom ≫
        (modulePullbackDerived f).map (tensorObjIsoBifunctor K L).hom ≫
          moduleDerivedPullbackTensorComparison f K.obj L.obj ≫
            (DerivedTensor.Bifunctor.functor (C := Modules X)).map
                (Prod.mkHom
                  ((pullback.inclusionIso f).inv.app K)
                  ((pullback.inclusionIso f).inv.app L)) ≫
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
theorem isIso_projectionFormulaMate (K : DerivedQCoh Y) (E : DerivedQCoh X) :
    IsIso (projectionFormulaMate f K E) :=
  sorry

/-- Canonical 08IN projection-formula isomorphism
`Rf_*(Lf^*K ⊗^L E) ≅ K ⊗^L Rf_*E`. -/
noncomputable def projectionFormulaIso (K : DerivedQCoh Y) (E : DerivedQCoh X) :
    (pushforwardCohomologyIn f).obj (tensorObj ((pullback f).obj K) E) ≅
      tensorObj K ((pushforwardCohomologyIn f).obj E) :=
  (@asIso _ _ _ _ (projectionFormulaMate f K E) (isIso_projectionFormulaMate f K E)).symm

/-- The forward map of `projectionFormulaIso` is the inverse of the projection-formula mate. -/
theorem projectionFormulaIso_hom (K : DerivedQCoh Y) (E : DerivedQCoh X) :
    (projectionFormulaIso f K E).hom =
      (@asIso _ _ _ _ (projectionFormulaMate f K E)
        (isIso_projectionFormulaMate f K E)).inv :=
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

/-- Specializing the tensor of the counit to `𝒪_Y` and applying the identity comparison on `K`
gives `K ⊗^L Rf_* a(𝒪_Y) ⟶ K`. -/
noncomputable def tensorCounitToUnit
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (K : DerivedQCoh Y) :
    tensorObj K ((pushforwardCohomologyIn f).obj (a.obj (structureSheaf Y))) ⟶ K :=
  tensorCounitMap f a aAdjunction K (structureSheaf Y) ≫ tensorUnitor K

/-- `tensorCounitToUnit` is the counit tensor map followed by the identity comparison on `K`. -/
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

/-- The canonical comparison `Lf^*K ⊗^L a(𝒪_Y) ⟶ a(K)` obtained from the 08IN projection
formula and the counit of `Rf_* ⊣ a`. -/
noncomputable def pullbackTensorDualityMap
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (K : DerivedQCoh Y) :
    tensorObj ((pullback f).obj K) (a.obj (structureSheaf Y)) ⟶ a.obj K :=
  aAdjunction.homEquiv _ _
    ((projectionFormulaIso f K (a.obj (structureSheaf Y))).hom ≫
      tensorCounitToUnit f a aAdjunction K)

/-- Transposing `pullbackTensorDualityMap` recovers the 08IN projection formula followed by the
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

/-- The duality comparison sends distinguished triangles in `K` to morphisms of triangles. -/
noncomputable def pullbackTensorDuality_distinguishedTriangle
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    [a.CommShift ℤ]
    [(pullback f ⋙ tensorRight (a.obj (structureSheaf Y))).CommShift ℤ]
    (T : Triangle (DerivedQCoh Y))
    (_hT : T ∈ distTriang (DerivedQCoh Y)) :
    TriangleMorphism
      ((pullback f ⋙ tensorRight (a.obj (structureSheaf Y))).mapTriangle.obj T)
      (a.mapTriangle.obj T) where
  hom₁ := pullbackTensorDualityMap f a aAdjunction T.obj₁
  hom₂ := pullbackTensorDualityMap f a aAdjunction T.obj₂
  hom₃ := pullbackTensorDualityMap f a aAdjunction T.obj₃
  comm₁ := sorry
  comm₂ := sorry
  comm₃ := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
