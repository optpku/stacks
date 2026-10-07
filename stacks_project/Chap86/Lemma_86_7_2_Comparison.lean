module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Algebra.Homology.Additive
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import stacks_project.Chap69.Lemma_69_13_2_IdealPower
public import stacks_project.Chap69.Lemma_69_17_2_Pullback
public import stacks_project.Chap75.Definition_75_20_2_TorIndependence
public import stacks_project.Chap86.Lemma_86_4_1_BaseChange
public import stacks_project.Chap86.«86_7_0_1_Comparison»

/-!
# Tensor-duality comparison and derived base change on algebraic spaces

For a Tor-independent cartesian square of algebraic spaces, the 86.7.0.1 maps
`Lf^*K ⊗^L a(𝒪_Y) ⟶ a(K)` and `L(f')^* Lg^*K ⊗^L a'(𝒪_{Y'}) ⟶ a'(Lg^*K)` fit in a
commutative square whose vertical arrows are the pullback-tensor/square comparison and
the 86.4.1.1 right-adjoint mate.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.DerivedCategory CategoryTheory.Limits ObjectProperty
open CategoryTheory.MonoidalCategory ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}}

/-- The objectwise comparison from iterated `DerivedQCoh` pullback to pullback along a
composite morphism of algebraic spaces. -/
noncomputable def pullbackCompAppIso {X Y Z : AlgebraicSpace S} (f : Y ⟶ Z) (g : Z ⟶ X)
    [IsIso (modulePullbackDerived.compComparison f g)] (K : DerivedQCoh X) :
    (pullback f).obj ((pullback g).obj K) ≅ (pullback (f ≫ g)).obj K :=
  (derivedQuasiCoherentModuleProperty Y).fullyFaithfulι.preimageIso <|
    (pullback.inclusionIso f).app ((pullback g).obj K) ≪≫
      (modulePullbackDerived f).mapIso ((pullback.inclusionIso g).app K) ≪≫
      (asIso (modulePullbackDerived.compComparison f g)).app K.obj ≪≫
      ((pullback.inclusionIso (f ≫ g)).app K).symm

/-- The underlying morphism of `pullbackCompAppIso` is the composite of the quasi-coherent
inclusions with the ambient derived composition comparison. -/
theorem pullbackCompAppIso_hom {X Y Z : AlgebraicSpace S} (f : Y ⟶ Z) (g : Z ⟶ X)
    [IsIso (modulePullbackDerived.compComparison f g)] (K : DerivedQCoh X) :
    ((pullbackCompAppIso f g K).hom).hom =
      (pullback.inclusionIso f).hom.app ((pullback g).obj K) ≫
        (modulePullbackDerived f).map ((pullback.inclusionIso g).hom.app K) ≫
          (modulePullbackDerived.compComparison f g).app K.obj ≫
            (pullback.inclusionIso (f ≫ g)).inv.app K :=
  sorry

/-- The canonical comparison between the two iterated derived pullbacks around a
commutative square of algebraic spaces. -/
noncomputable def pullbackSquareAppIso {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [IsIso (modulePullbackDerived.compComparison g' f)]
    [IsIso (modulePullbackDerived.compComparison f' g)]
    (sq : CommSq g' f' f g) (K : DerivedQCoh Y) :
    (pullback g').obj ((pullback f).obj K) ≅
      (pullback f').obj ((pullback g).obj K) :=
  pullbackCompAppIso g' f K ≪≫
    eqToIso (congrArg (fun h : X' ⟶ Y ↦ (pullback h).obj K) sq.w) ≪≫
    (pullbackCompAppIso f' g K).symm

/-- The underlying morphism of `pullbackSquareAppIso` is the composite of the two
composition comparisons with the identification `g' ≫ f = f' ≫ g`. -/
theorem pullbackSquareAppIso_hom {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [IsIso (modulePullbackDerived.compComparison g' f)]
    [IsIso (modulePullbackDerived.compComparison f' g)]
    (sq : CommSq g' f' f g) (K : DerivedQCoh Y) :
    (pullbackSquareAppIso g' f' f g sq K).hom =
      (pullbackCompAppIso g' f K).hom ≫
        (eqToIso (congrArg (fun h : X' ⟶ Y ↦ (pullback h).obj K) sq.w)).hom ≫
          (pullbackCompAppIso f' g K).inv :=
  sorry

/-- Ordinary pullback of the module tensor unit compared with the tensor unit of the source,
via the structure-module identification and the adjunct of `𝒪_Y ⟶ h_* 𝒪_X`. -/
noncomputable def modulesPullbackTensorUnitMap {X Y : AlgebraicSpace S} (h : X ⟶ Y) :
    (Modules.pullback h).obj (tensorUnit (Modules Y)) ⟶ tensorUnit (Modules X) :=
  (Modules.pullback h).map (Modules.structureModuleIsoTensorUnit Y).inv ≫
    IdealSubobject.pullbackUnit h ≫
    (Modules.structureModuleIsoTensorUnit X).hom

/-- Ordinary pullback of the tensor unit is an isomorphism after identifying structure
modules with tensor units. -/
theorem isIso_modulesPullbackTensorUnitMap {X Y : AlgebraicSpace S} (h : X ⟶ Y) :
    IsIso (modulesPullbackTensorUnitMap h) :=
  sorry

/-- The comparison `Lg^* 𝒪_Y ⟶ 𝒪_X` on complexes with quasi-coherent cohomology. -/
noncomputable def pullbackStructureSheafMap {X Y : AlgebraicSpace S} (h : X ⟶ Y) :
    (pullback h).obj (structureSheaf Y) ⟶ structureSheaf X :=
  ObjectProperty.homMk <|
    (pullback.inclusionIso h).hom.app (structureSheaf Y) ≫
      (modulePullbackDerived h).map (structureSheafUnitIso Y).hom ≫
        modulePullbackDerived_cochainCounit h
          ((CochainComplex.singleFunctor (Modules Y) (0 : ℤ)).obj
            (tensorUnit (Modules Y))) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex
              (Modules.pullback h) (up ℤ) (0 : ℤ)).hom.app
            (tensorUnit (Modules Y))) ≫
        DerivedCategory.Q.map
          ((CochainComplex.singleFunctor (Modules X) (0 : ℤ)).map
            (modulesPullbackTensorUnitMap h)) ≫
        (structureSheafUnitIso X).inv

/-- The underlying morphism of `pullbackStructureSheafMap` is the included derived counit,
the single-complex identification, and the tensor-unit pullback. -/
theorem pullbackStructureSheafMap_spec {X Y : AlgebraicSpace S} (h : X ⟶ Y) :
    (pullbackStructureSheafMap h).hom =
      (pullback.inclusionIso h).hom.app (structureSheaf Y) ≫
        (modulePullbackDerived h).map (structureSheafUnitIso Y).hom ≫
          modulePullbackDerived_cochainCounit h
            ((CochainComplex.singleFunctor (Modules Y) (0 : ℤ)).obj
              (tensorUnit (Modules Y))) ≫
          DerivedCategory.Q.map
            ((HomologicalComplex.singleMapHomologicalComplex
                (Modules.pullback h) (up ℤ) (0 : ℤ)).hom.app
              (tensorUnit (Modules Y))) ≫
          DerivedCategory.Q.map
            ((CochainComplex.singleFunctor (Modules X) (0 : ℤ)).map
              (modulesPullbackTensorUnitMap h)) ≫
          (structureSheafUnitIso X).inv :=
  sorry

variable {X' X Y' Y : AlgebraicSpace S}

/-- The dual of the 86.4.1.1 mate, obtained by viewing the Tor-independent right mate as an
isomorphism `a' ⋙ Rg'_* ≅ Rg_* ⋙ a`. -/
noncomputable def dualRightMateIso
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
    [IsIso (modulePullbackDerived.compComparison f' g)]
    [IsIso (modulePullbackDerived.compComparison g' f)]
    (sq : IsPullback g' f' f g)
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (fAdj : pushforwardCohomologyIn f ⊣ a) (f'Adj : pushforwardCohomologyIn f' ⊣ a')
    (hTor : TorIndependentOver (Over.mk f) (Over.mk g)) :
    a' ⋙ pushforwardCohomologyIn g' ≅ pushforwardCohomologyIn g ⋙ a :=
  @asIso _ _ _ _
    (BaseChange.rightMate g' f' f g sq.toCommSq a a' fAdj f'Adj)
    (BaseChange.rightMate_isIso_of_torIndependent
      g' f' f g sq a a' fAdj f'Adj hTor)

/-- The forward map of `dualRightMateIso` is the right-adjoint mate of derived base change. -/
theorem dualRightMateIso_hom
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
    [IsIso (modulePullbackDerived.compComparison f' g)]
    [IsIso (modulePullbackDerived.compComparison g' f)]
    (sq : IsPullback g' f' f g)
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (fAdj : pushforwardCohomologyIn f ⊣ a) (f'Adj : pushforwardCohomologyIn f' ⊣ a')
    (hTor : TorIndependentOver (Over.mk f) (Over.mk g)) :
    (dualRightMateIso g' f' f g sq a a' fAdj f'Adj hTor).hom =
      BaseChange.rightMate g' f' f g sq.toCommSq a a' fAdj f'Adj :=
  sorry

/-- The 86.4.1.1 component: right-adjoint base change of a chosen dual isomorphism,
evaluated at `K`. -/
noncomputable def rightAdjointBaseChangeMap
    (g' : X' ⟶ X) (g : Y' ⟶ Y)
    [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (dualBaseChangeIso : a' ⋙ pushforwardCohomologyIn g' ≅ pushforwardCohomologyIn g ⋙ a)
    (K : DerivedQCoh Y) :
    (pullback g').obj (a.obj K) ⟶ a'.obj ((pullback g).obj K) :=
  (DerivedBaseChange.mapOfRight
    (pullbackPushforwardCohomologyAdjunction g)
    (pullbackPushforwardCohomologyAdjunction g')
    dualBaseChangeIso.inv).app K

/-- `rightAdjointBaseChangeMap` is the objectwise right mate of the inverse dual
base-change isomorphism. -/
theorem rightAdjointBaseChangeMap_spec
    (g' : X' ⟶ X) (g : Y' ⟶ Y)
    [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (dualBaseChangeIso : a' ⋙ pushforwardCohomologyIn g' ≅ pushforwardCohomologyIn g ⋙ a)
    (K : DerivedQCoh Y) :
    rightAdjointBaseChangeMap g' g a a' dualBaseChangeIso K =
      (DerivedBaseChange.mapOfRight
        (pullbackPushforwardCohomologyAdjunction g)
        (pullbackPushforwardCohomologyAdjunction g')
        dualBaseChangeIso.inv).app K :=
  sorry

/-- The left vertical arrow of the tensor-duality base-change square: distribute pullback
over tensor, identify the two iterated pullbacks, and apply right-adjoint base change to
the structure-sheaf factor. -/
noncomputable def pullbackTensorDualityBaseChangeMap
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
    [IsIso (modulePullbackDerived.compComparison g' f)]
    [IsIso (modulePullbackDerived.compComparison f' g)]
    (sq : CommSq g' f' f g)
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (dualBaseChangeIso : a' ⋙ pushforwardCohomologyIn g' ≅ pushforwardCohomologyIn g ⋙ a)
    (K : DerivedQCoh Y) :
    (pullback g').obj (tensorObj ((pullback f).obj K) (a.obj (structureSheaf Y))) ⟶
      tensorObj ((pullback f').obj ((pullback g).obj K)) (a'.obj (structureSheaf Y')) :=
  pullbackTensorComparison g' ((pullback f).obj K) (a.obj (structureSheaf Y)) ≫
    tensorMap
      (pullbackSquareAppIso g' f' f g sq K).hom
      (rightAdjointBaseChangeMap g' g a a' dualBaseChangeIso (structureSheaf Y) ≫
        a'.map (pullbackStructureSheafMap g))

/-- The tensor-duality base-change map is the pullback-tensor comparison followed by the
square and right-adjoint comparisons on the two factors. -/
theorem pullbackTensorDualityBaseChangeMap_spec
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
    [IsIso (modulePullbackDerived.compComparison g' f)]
    [IsIso (modulePullbackDerived.compComparison f' g)]
    (sq : CommSq g' f' f g)
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (dualBaseChangeIso : a' ⋙ pushforwardCohomologyIn g' ≅ pushforwardCohomologyIn g ⋙ a)
    (K : DerivedQCoh Y) :
    pullbackTensorDualityBaseChangeMap g' f' f g sq a a' dualBaseChangeIso K =
      pullbackTensorComparison g' ((pullback f).obj K) (a.obj (structureSheaf Y)) ≫
        tensorMap
          (pullbackSquareAppIso g' f' f g sq K).hom
          (rightAdjointBaseChangeMap g' g a a' dualBaseChangeIso (structureSheaf Y) ≫
            a'.map (pullbackStructureSheafMap g)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
