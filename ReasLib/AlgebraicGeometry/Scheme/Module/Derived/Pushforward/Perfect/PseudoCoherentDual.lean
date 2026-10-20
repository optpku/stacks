/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.Perfect
public import ReasLib.CategoryTheory.Monoidal.Closed.Duality

@[expose] public section

open CategoryTheory
open scoped CartesianClosed

noncomputable section

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

namespace AlgebraicGeometry.Scheme.ModuleDerived

/-- For a proper flat finitely presented morphism to a quasi-compact quasi-separated scheme,
the pushforward of the internal Hom from a pseudo-coherent complex to a relatively perfect
complex is the dual of a pseudo-coherent complex. The same complex gives this description after
every cartesian base change. -/
theorem exists_pseudoCoherent_dual {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S]
    [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f]
    [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase f.toShHom).restrict U.isOpenEmbedding))]
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    [MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)]
    (E K : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : IsPerfectRelativeTo f E)
    (hK : RingedSpace.ModuleDerived.IsPseudoCoherent K) :
    ∃ L : RingedSpace.ModuleDerived S.toRingedSpace,
      RingedSpace.ModuleDerived.IsPseudoCoherent L ∧
        IsIsomorphic
          ((RingedSpace.moduleDerivedPushforward f.toShHom).obj (K ⟹ E))
          (MonoidalClosed.dual L) ∧
        ∀ {X' S' : Scheme.{u}}
          [MonoidalCategory (RingedSpace.ModuleDerived X'.toRingedSpace)]
          [MonoidalClosed (RingedSpace.ModuleDerived X'.toRingedSpace)]
          [MonoidalCategory (RingedSpace.ModuleDerived S'.toRingedSpace)]
          [MonoidalClosed (RingedSpace.ModuleDerived S'.toRingedSpace)]
          (g' : X' ⟶ X) (f' : X' ⟶ S') (g : S' ⟶ S),
          IsPullback g' f' f g →
            IsIsomorphic
              ((RingedSpace.moduleDerivedPushforward f'.toShHom).obj
                ((RingedSpace.modulePullbackDerived g'.toShHom).obj K ⟹
                  (RingedSpace.modulePullbackDerived g'.toShHom).obj E))
              (MonoidalClosed.dual
                ((RingedSpace.modulePullbackDerived g.toShHom).obj L)) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
