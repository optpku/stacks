/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Derived.Commutation
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.ChernClass

/- Lemma 42.46.6 (1): for a perfect derived module whose Chern classes are defined, the
canonical derived Chern class `c_p(E)` is in the center of `A^*(X)`. -/
@[stacks 0FAC]
#check
  (AlgebraicGeometry.ChernClass.Derived.component_mem_center :
    ∀ {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
      (π : X ⟶ S) [LocallyOfFiniteType π]
      (classes : Theory δ π) (E : RingedSpace.ModuleDerived X.toRingedSpace)
      (hPerfect : RingedSpace.ModuleDerived.IsPerfect E)
      (hDefined :
        ∃ (Y : Scheme.{u}) (f : Y ⟶ X),
          IsEnvelope f ∧
            RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
              ((RingedSpace.modulePullbackDerived f.toShHom).obj E))
      (p : ℕ),
      DirectSum.of (ChowCohomology.degree δ π) (p : ℤ)
          (LocalizedChern.EnvelopeCaps.derivedClass δ (X := Over.mk π) classes E
            hPerfect hDefined true p) ∈
        Set.center (ChowCohomology.ring δ π))

/- Lemma 42.46.6 (2): if `g : X' → X` is locally of finite type and `c ∈ A^*(X' → X)`, then
`c ∘ c_p(E) = c_p(Lg^*E) ∘ c`. -/
@[stacks 0FAC]
#check
  (AlgebraicGeometry.ChernClass.Derived.comp_component :
    ∀ {S X X' : Scheme.{u}} [UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
      (classes : Theory δ π) (E : RingedSpace.ModuleDerived X.toRingedSpace)
      (hPerfect : RingedSpace.ModuleDerived.IsPerfect E)
      (hDefined :
        ∃ (Y : Scheme.{u}) (f : Y ⟶ X),
          IsEnvelope f ∧
            RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
              ((RingedSpace.modulePullbackDerived f.toShHom).obj E))
      (p : ℕ) (g : X' ⟶ X) [LocallyOfFiniteType g] (q : ℤ)
      (c : BivariantClass δ (Over.homMk g : Over.mk (g ≫ π) ⟶ Over.mk π) q),
      HEq
        (BivariantClass.comp δ (Over.homMk g : Over.mk (g ≫ π) ⟶ Over.mk π)
          (𝟙 (Over.mk π)) c
          (LocalizedChern.EnvelopeCaps.derivedClass δ (X := Over.mk π) classes E
            hPerfect hDefined true p))
        (BivariantClass.comp δ (𝟙 (Over.mk (g ≫ π)))
          (Over.homMk g : Over.mk (g ≫ π) ⟶ Over.mk π)
          (LocalizedChern.EnvelopeCaps.derivedClass δ (X := Over.mk (g ≫ π))
            (classes.reanchor (Over.mk (g ≫ π)))
            ((RingedSpace.modulePullbackDerived g.toShHom).obj E)
            (RingedSpace.modulePullbackDerived_isPerfect g.toShHom E hPerfect)
            (LocalizedChern.EnvelopeCaps.defined_pullback g E hDefined) true p) c))

end AlgebraicGeometry.ChernClass
