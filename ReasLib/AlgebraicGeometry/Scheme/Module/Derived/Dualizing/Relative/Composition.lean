/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Relative

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

namespace AlgebraicGeometry.Scheme.RelativeDualizingComplex

/-- Composition of relative dualizing complexes along flat finitely presented scheme morphisms. -/
theorem trans
    {S X Y : Scheme.{u}} (f : Y ⟶ X) (g : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] [QuasiCompact f]
    [Flat g] [LocallyOfFinitePresentation g] [QuasiCompact g]
    [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase f.toShHom).restrict U.isOpenEmbedding))]
    [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase g.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase g.toShHom).restrict U.isOpenEmbedding))]
    [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase (f ≫ g).toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase (f ≫ g).toShHom).restrict U.isOpenEmbedding))]
    (WK : (pullback g g).Opens) (δK : X ⟶ WK.toScheme) [IsClosedImmersion δK]
    (hδK : δK ≫ WK.ι = pullback.diagonal g)
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [MonoidalCategory (RingedSpace.ModuleDerived WK.toScheme.toRingedSpace)]
    [(RingedSpace.moduleDerivedPushforward δK.toShHom).LaxMonoidal]
    (HK : MonoidalClosed (RingedSpace.ModuleDerived WK.toScheme.toRingedSpace))
    (K : Scheme.RelativeDualizingComplex g WK δK hδK HK)
    (WM : (pullback f f).Opens) (δM : Y ⟶ WM.toScheme) [IsClosedImmersion δM]
    (hδM : δM ≫ WM.ι = pullback.diagonal f)
    [MonoidalCategory (RingedSpace.ModuleDerived Y.toRingedSpace)]
    [MonoidalCategory (RingedSpace.ModuleDerived WM.toScheme.toRingedSpace)]
    [(RingedSpace.moduleDerivedPushforward δM.toShHom).LaxMonoidal]
    (HM : MonoidalClosed (RingedSpace.ModuleDerived WM.toScheme.toRingedSpace))
    (M : Scheme.RelativeDualizingComplex f WM δM hδM HM)
    (W : (pullback (f ≫ g) (f ≫ g)).Opens) (δ : Y ⟶ W.toScheme)
    [IsClosedImmersion δ] (hδ : δ ≫ W.ι = pullback.diagonal (f ≫ g))
    [MonoidalCategory (RingedSpace.ModuleDerived W.toScheme.toRingedSpace)]
    [(RingedSpace.moduleDerivedPushforward δ.toShHom).LaxMonoidal]
    (H : MonoidalClosed (RingedSpace.ModuleDerived W.toScheme.toRingedSpace)) :
    let E := M.complex ⊗
      (RingedSpace.modulePullbackDerived f.toShHom).obj K.complex
    ∃ ζ : (diagonalAlgebra δ).X ⟶
        (RingedSpace.modulePullbackDerived
          (W.ι ≫ pullback.fst (f ≫ g) (f ≫ g)).toShHom).obj E,
      ModuleDerived.IsPerfectRelativeTo (f ≫ g) E ∧
        IsIso (dualityMap δ H ζ) := sorry

end AlgebraicGeometry.Scheme.RelativeDualizingComplex
