/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Composition
public import ReasLib.AlgebraicGeometry.ChowCohomology
public import ReasLib.AlgebraicGeometry.LocalizedChern.DerivedEnvelopeCaps.BaseChange
public import Mathlib.Algebra.Group.Center

/-!
# Commutativity of derived Chern classes

For a perfect derived module `E` on `X` whose Chern classes are defined, the canonical derived
Chern class `c_p(E)` is the envelope-descended total Chern class
`LocalizedChern.EnvelopeCaps.derivedClass … true p`. It commutes with every bivariant class
after locally finite-type pullback, `c ∘ c_p(E) = c_p(Lg^*E) ∘ c`, and is therefore central in
`A^*(X)`. The bounded constant-rank case used in the source proof is part of the proof debt,
not a hypothesis.
-/

@[expose] public section

open CategoryTheory
open scoped DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.ChernClass.Derived

/-- For a perfect derived module `E` with defined Chern classes, a locally finite-type
morphism `g : X' ⟶ X` and `c ∈ A^q(X' → X)`, one has `c ∘ c_p(E) = c_p(Lg^*E) ∘ c`; the two
composites live over the definitionally different morphisms `g ≫ 𝟙` and `𝟙 ≫ g` and in
degrees `q + p` and `p + q`, so they are compared by `HEq`. -/
theorem comp_component
    {S X X' : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (classes : Theory δ π) (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E)
    (hDefined :
      ∃ (Y : Scheme.{u}) (f : Y ⟶ X),
        IsEnvelope f ∧
          RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
            ((RingedSpace.modulePullbackDerived f.toShHom).obj E))
    (p : ℕ) (g : X' ⟶ X) [LocallyOfFiniteType g] (q : ℤ)
    (c : BivariantClass δ (Over.homMk g : Over.mk (g ≫ π) ⟶ Over.mk π) q) :
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
          (LocalizedChern.EnvelopeCaps.defined_pullback g E hDefined) true p) c) := sorry

/-- For a perfect derived module with defined Chern classes, the canonical derived Chern class
`c_p(E)` belongs to the center of the full operational Chow cohomology ring `A^*(X)`. -/
theorem component_mem_center
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (classes : Theory δ π) (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E)
    (hDefined :
      ∃ (Y : Scheme.{u}) (f : Y ⟶ X),
        IsEnvelope f ∧
          RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
            ((RingedSpace.modulePullbackDerived f.toShHom).obj E))
    (p : ℕ) :
    DirectSum.of (ChowCohomology.degree δ π) (p : ℤ)
        (LocalizedChern.EnvelopeCaps.derivedClass δ (X := Over.mk π) classes E
          hPerfect hDefined true p) ∈
      Set.center (ChowCohomology.ring δ π) := sorry

end AlgebraicGeometry.ChernClass.Derived
