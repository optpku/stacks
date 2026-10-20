module

public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.DerivedCategory.Bounded
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap75.Lemma_75_22_1
public import stacks_project.Chap76.Definition_76_47_1_Perfect
public import stacks_project.Chap86.Lemma_86_4_1_BaseChange

/-!
# Right-adjoint derived base change on affine bases

In a cartesian Tor-independent square of algebraic spaces, with affine bases and
proper vertical map, the 86.4.1.1 mate of the dual right-adjoint comparison is an
isomorphism under the three extra hypotheses of Stacks Lemma 86.5.1.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.BaseChange

variable {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}

/-- For a Tor-independent cartesian square of quasi-compact, quasi-separated algebraic
spaces with affine bases and a proper flat finitely presented vertical map, the
right-adjoint base-change map is an isomorphism on every unbounded quasi-coherent
complex. -/
theorem mapOfRight_app_isIso_of_flat
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
    [IsIso (modulePullbackDerived.compComparison f' g)]
    [IsIso (modulePullbackDerived.compComparison g' f)]
    [IsAffine Y] [IsAffine Y'] [Proper f] [Flat f] [FinitePresentation f]
    (sq : IsPullback g' f' f g)
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (fAdj : pushforwardCohomologyIn f ⊣ a)
    (f'Adj : pushforwardCohomologyIn f' ⊣ a')
    (hTor : TorIndependentOver (Over.mk f) (Over.mk g))
    (dualBaseChangeIso :
      a' ⋙ pushforwardCohomologyIn g' ≅ pushforwardCohomologyIn g ⋙ a)
    (h_dualBaseChange : dualBaseChangeIso.hom =
      rightMate g' f' f g sq.toCommSq a a' fAdj f'Adj)
    (K : DerivedQCoh Y) :
    IsIso
      ((DerivedBaseChange.mapOfRight
        (pullbackPushforwardCohomologyAdjunction g)
        (pullbackPushforwardCohomologyAdjunction g')
        dualBaseChangeIso.inv).app K) := sorry

/-- For a Tor-independent cartesian square of quasi-compact, quasi-separated algebraic
spaces with affine bases, Noetherian target, and a proper perfect vertical map, the
right-adjoint base-change map is an isomorphism on every unbounded quasi-coherent
complex. -/
theorem mapOfRight_app_isIso_of_perfect
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
    [IsIso (modulePullbackDerived.compComparison f' g)]
    [IsIso (modulePullbackDerived.compComparison g' f)]
    [IsAffine Y] [IsAffine Y'] [Proper f] [Perfect f] [IsNoetherian Y]
    (sq : IsPullback g' f' f g)
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (fAdj : pushforwardCohomologyIn f ⊣ a)
    (f'Adj : pushforwardCohomologyIn f' ⊣ a')
    (hTor : TorIndependentOver (Over.mk f) (Over.mk g))
    (dualBaseChangeIso :
      a' ⋙ pushforwardCohomologyIn g' ≅ pushforwardCohomologyIn g ⋙ a)
    (h_dualBaseChange : dualBaseChangeIso.hom =
      rightMate g' f' f g sq.toCommSq a a' fAdj f'Adj)
    (K : DerivedQCoh Y) :
    IsIso
      ((DerivedBaseChange.mapOfRight
        (pullbackPushforwardCohomologyAdjunction g)
        (pullbackPushforwardCohomologyAdjunction g')
        dualBaseChangeIso.inv).app K) := sorry

/-- For a Tor-independent cartesian square of quasi-compact, quasi-separated algebraic
spaces with affine bases, Noetherian target, proper vertical map, and finite Tor
dimension of `𝒪_{Y'}` over `g`, the right-adjoint base-change map is an isomorphism
on every bounded-below quasi-coherent complex. -/
theorem mapOfRight_app_isIso_of_finiteTorDimension
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [∀ sq : EtaleSquare g,
      (Functor.Homotopy.toDerived
        (SmallEtaleModuleGlueing.restrictFunctor_hom sq.left ⋙
          Modules.restrictToScheme sq.left.left ⋙
          Scheme.Modules.toRingedSpace sq.left.left.left)).HasLeftDerivedFunctor (ModuleQis Y')]
    [∀ sq : EtaleSquare g, DerivedCategory.DerivedTensor.Right.Has
      (C := RingedSpace.Modules (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom))]
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
    [IsIso (modulePullbackDerived.compComparison f' g)]
    [IsIso (modulePullbackDerived.compComparison g' f)]
    [IsAffine Y] [IsAffine Y'] [Proper f] [IsNoetherian Y]
    (sq : IsPullback g' f' f g)
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (fAdj : pushforwardCohomologyIn f ⊣ a)
    (f'Adj : pushforwardCohomologyIn f' ⊣ a')
    (hTor : TorIndependentOver (Over.mk f) (Over.mk g))
    (dualBaseChangeIso :
      a' ⋙ pushforwardCohomologyIn g' ≅ pushforwardCohomologyIn g ⋙ a)
    (h_dualBaseChange : dualBaseChangeIso.hom =
      rightMate g' f' f g sq.toCommSq a a' fAdj f'Adj)
    (K : DerivedQCoh Y) (hK : K.obj.IsBoundedBelow)
    (h_finiteTor : ModuleDerived.HasFiniteTorDimensionOver g (structureSheaf Y').obj) :
    IsIso
      ((DerivedBaseChange.mapOfRight
        (pullbackPushforwardCohomologyAdjunction g)
        (pullbackPushforwardCohomologyAdjunction g')
        dualBaseChangeIso.inv).app K) := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.BaseChange
