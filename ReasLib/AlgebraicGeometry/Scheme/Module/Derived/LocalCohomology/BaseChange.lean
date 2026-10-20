module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedSubset.Derived.BaseChange.InverseImage
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.PrincipalOpen.LocalCohomology.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.LocalCohomology.FundamentalClass
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedSubset.Derived.BaseChange

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape TopologicalSpace
open SheafOfModules.ClosedSubset
open AlgebraicGeometry.RingedSpace.ModuleDerived.Cohomology
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.LocalCohomology.BaseChange

variable {Z' X' Z X : Scheme.{u}}

/-- A cartesian square of closed immersions identifies the inverse image of the lower
closed support with the upper closed support. -/
theorem support_preimage (h : Z' ⟶ Z) (i' : Z' ⟶ X') (i : Z ⟶ X) (g : X' ⟶ X)
    [IsClosedImmersion i'] [IsClosedImmersion i] (sq : IsPullback h i' i g) :
    RingedSpace.ClosedSubset.preimage g.toLRSHom.toShHom i.ker.support =
      i'.ker.support := sorry

/-- Derived pullback between modules supported on equal inverse-image closed subsets. -/
noncomputable def restrictedDerivedPullback (g : X' ⟶ X) (Z : Closeds X)
    (Z' : Closeds X')
    (hZ : RingedSpace.ClosedSubset.preimage g.toLRSHom.toShHom Z = Z') :
    ModuleDerived X.toRingedSpace.ringCatSheaf Z ⥤
      ModuleDerived X'.toRingedSpace.ringCatSheaf Z' :=
  hZ ▸ RingedSpace.ClosedSubset.InverseImage.derivedPullback g.toLRSHom.toShHom Z

/-- The derived-pushforward comparison for pullback to a specified inverse-image closed
subset. -/
noncomputable def restrictedDerivedPushforwardIso (g : X' ⟶ X) (Z : Closeds X)
    (Z' : Closeds X')
    (hZ : RingedSpace.ClosedSubset.preimage g.toLRSHom.toShHom Z = Z') :
    restrictedDerivedPullback g Z Z' hZ ⋙
        Derived.pushforward X'.toRingedSpace.ringCatSheaf Z' ≅
      Derived.pushforward X.toRingedSpace.ringCatSheaf Z ⋙
        RingedSpace.modulePullbackDerived g.toLRSHom.toShHom :=
  match hZ with
  | rfl => RingedSpace.ClosedSubset.InverseImage.derivedPushforwardIso
      g.toLRSHom.toShHom Z

/-- The ambient derived object whose degree-`c` homology is local cohomology supported on
the image of a closed immersion. -/
noncomputable abbrev supportedObject (i : Z ⟶ X) [IsClosedImmersion i]
    (F : Scheme.QCoh X) : RingedSpace.ModuleDerived X.toRingedSpace :=
  (Derived.pushforward X.toRingedSpace.ringCatSheaf i.ker.support).obj
    ((Derived.sectionsWithSupport X.toRingedSpace.ringCatSheaf i.ker.support).obj
      ((ModuleCech.moduleToDerived X).obj ((Scheme.QCoh.inclusion X).obj F)))

/-- For a finitely presented closed immersion with rank-`c` locally free conormal sheaf,
the supported derived object of a quasicoherent module is bounded above by `c`. -/
theorem supportedObject_isLE (i : Z ⟶ X) [IsClosedImmersion i]
    [Scheme.Hom.FinitePresentation i] (c : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)]
    (F : Scheme.QCoh X) :
    (supportedObject i F).IsLE (c : ℤ) := sorry

/-- The canonical comparison from derived pullback of a quasicoherent module in degree zero
to the degree-zero realization of its quasicoherent pullback. -/
noncomputable def coefficientComparison (g : X' ⟶ X) (F : Scheme.QCoh X) :
    (RingedSpace.modulePullbackDerived g.toLRSHom.toShHom).obj
        ((ModuleCech.moduleToDerived X).obj ((Scheme.QCoh.inclusion X).obj F)) ⟶
      (ModuleCech.moduleToDerived X').obj
        ((Scheme.QCoh.inclusion X').obj ((Scheme.QCoh.pullback g).obj F)) :=
  ModuleCech.BaseChange.coefficientComparison g ((Scheme.QCoh.inclusion X).obj F) ≫
    (ModuleCech.moduleToDerived X').map
      (eqToHom (Scheme.QCoh.pullback_obj g F).symm)

/-- The derived base-change morphism between the ambient derived objects with support. -/
noncomputable def derivedMap (h : Z' ⟶ Z) (i' : Z' ⟶ X') (i : Z ⟶ X)
    (g : X' ⟶ X) [IsClosedImmersion i'] [IsClosedImmersion i]
    (sq : IsPullback h i' i g) (F : Scheme.QCoh X) :
    (RingedSpace.modulePullbackDerived g.toLRSHom.toShHom).obj
        (supportedObject i F) ⟶
      supportedObject i' ((Scheme.QCoh.pullback g).obj F) :=
  let hZ := support_preimage h i' i g sq
  let squareIso := restrictedDerivedPushforwardIso g i.ker.support i'.ker.support hZ
  let sourceSupport :=
    (Derived.sectionsWithSupport X.toRingedSpace.ringCatSheaf i.ker.support).obj
      ((ModuleCech.moduleToDerived X).obj ((Scheme.QCoh.inclusion X).obj F))
  squareIso.inv.app sourceSupport ≫
    (Derived.pushforward X'.toRingedSpace.ringCatSheaf i'.ker.support).map
      (RingedSpace.ClosedSubset.DerivedBaseChange.app squareIso
          ((ModuleCech.moduleToDerived X).obj ((Scheme.QCoh.inclusion X).obj F)) ≫
        (Derived.sectionsWithSupport X'.toRingedSpace.ringCatSheaf i'.ker.support).map
          (coefficientComparison g F))

/-- The canonical degree-`c` local-cohomology base-change morphism for a cartesian square of
closed immersions. -/
noncomputable def map (h : Z' ⟶ Z) (i' : Z' ⟶ X') (i : Z ⟶ X) (g : X' ⟶ X)
    [IsClosedImmersion i'] [IsClosedImmersion i] [Scheme.Hom.FinitePresentation i]
    (c : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)]
    (sq : IsPullback h i' i g) (F : Scheme.QCoh X) :
    (Scheme.Modules.pullback g).obj ((Scheme.Hom.LocalCohomology.functor i c).obj F) ⟶
      (Scheme.Hom.LocalCohomology.functor i' c).obj
        ((Scheme.QCoh.pullback g).obj F) :=
  let sourceSupport :=
    (Derived.sectionsWithSupport X.toRingedSpace.ringCatSheaf i.ker.support).obj
      ((ModuleCech.moduleToDerived X).obj ((Scheme.QCoh.inclusion X).obj F))
  let targetSupport :=
    (Derived.sectionsWithSupport X'.toRingedSpace.ringCatSheaf i'.ker.support).obj
      ((ModuleCech.moduleToDerived X').obj
        ((Scheme.QCoh.inclusion X').obj ((Scheme.QCoh.pullback g).obj F)))
  (RingedSpace.Hom.pullback g.toLRSHom.toShHom).map
      (((ExactFunctor.of
        (SheafOfModules.ClosedSubset.pushforward
          X.toRingedSpace.ringCatSheaf i.ker.support)).homologyFunctorIso
          (c : ℤ)).inv.app sourceSupport) ≫
    upperPullbackComparison g.toLRSHom.toShHom (supportedObject i F) (c : ℤ)
      (supportedObject_isLE i c F) ≫
    (DerivedCategory.homologyFunctor X'.toRingedSpace.Modules (c : ℤ)).map
      (derivedMap h i' i g sq F) ≫
    ((ExactFunctor.of
      (SheafOfModules.ClosedSubset.pushforward
        X'.toRingedSpace.ringCatSheaf i'.ker.support)).homologyFunctorIso
        (c : ℤ)).hom.app targetSupport

/-- The local-cohomology base-change morphism is the upper-edge comparison followed by the
derived closed-support comparison and the two exact-pushforward identifications. -/
theorem map_def (h : Z' ⟶ Z) (i' : Z' ⟶ X') (i : Z ⟶ X) (g : X' ⟶ X)
    [IsClosedImmersion i'] [IsClosedImmersion i] [Scheme.Hom.FinitePresentation i]
    (c : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)]
    (sq : IsPullback h i' i g) (F : Scheme.QCoh X) :
    map h i' i g c sq F =
      let sourceSupport :=
        (Derived.sectionsWithSupport X.toRingedSpace.ringCatSheaf i.ker.support).obj
          ((ModuleCech.moduleToDerived X).obj ((Scheme.QCoh.inclusion X).obj F))
      let targetSupport :=
        (Derived.sectionsWithSupport X'.toRingedSpace.ringCatSheaf i'.ker.support).obj
          ((ModuleCech.moduleToDerived X').obj
            ((Scheme.QCoh.inclusion X').obj ((Scheme.QCoh.pullback g).obj F)))
      (RingedSpace.Hom.pullback g.toLRSHom.toShHom).map
          (((ExactFunctor.of
            (SheafOfModules.ClosedSubset.pushforward
              X.toRingedSpace.ringCatSheaf i.ker.support)).homologyFunctorIso
              (c : ℤ)).inv.app sourceSupport) ≫
        upperPullbackComparison g.toLRSHom.toShHom (supportedObject i F) (c : ℤ)
          (supportedObject_isLE i c F) ≫
        (DerivedCategory.homologyFunctor X'.toRingedSpace.Modules (c : ℤ)).map
          (derivedMap h i' i g sq F) ≫
        ((ExactFunctor.of
          (SheafOfModules.ClosedSubset.pushforward
            X'.toRingedSpace.ringCatSheaf i'.ker.support)).homologyFunctorIso
            (c : ℤ)).hom.app targetSupport := sorry

/-- Local-cohomology base change is natural in the quasicoherent coefficient module. -/
theorem map_naturality (h : Z' ⟶ Z) (i' : Z' ⟶ X') (i : Z ⟶ X) (g : X' ⟶ X)
    [IsClosedImmersion i'] [IsClosedImmersion i] [Scheme.Hom.FinitePresentation i]
    (c : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)]
    (sq : IsPullback h i' i g) {F G : Scheme.QCoh X} (a : F ⟶ G) :
    (Scheme.Modules.pullback g).map ((Scheme.Hom.LocalCohomology.functor i c).map a) ≫
        map h i' i g c sq G =
      map h i' i g c sq F ≫
        (Scheme.Hom.LocalCohomology.functor i' c).map ((Scheme.QCoh.pullback g).map a) := sorry

end AlgebraicGeometry.Scheme.Hom.LocalCohomology.BaseChange

end
