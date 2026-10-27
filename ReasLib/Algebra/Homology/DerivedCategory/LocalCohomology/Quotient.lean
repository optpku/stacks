/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.DerivedTorsion.Comparison
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleEmbedding

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.LocalCohomology

variable {A : Type u} [CommRing A]

/-- For a finitely generated ideal, the canonical comparison identifies degree-zero
ideal-power-torsion cohomology with degree-zero cohomology supported on its vanishing locus. -/
theorem h0IdealToClosedSupportIsIso (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{u} A)
    (RΓZ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓZ : IdealPowerTorsion.inclusion I ⊣ RΓZ) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat A) 0).map
      ((idealToClosedSupport I hI RΓZ hRΓZ).app (ModuleCat.single0 M)).hom) := sorry

/-- Degree-zero derived ideal-power-torsion cohomology vanishes after quotienting a module by
its ideal-power-torsion primary component. -/
theorem h0IdealQuotientPrimaryComponentIsZero (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{u} A) :
    letI : Fact I.FG := ⟨hI⟩
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
      (((ModuleCat.IdealPowerTorsion.derivedTorsion I ⋙
          CohomologyIn.Comparison.functor (ModuleCat.isIdealPowerTorsion I)).obj
        (ModuleCat.single0 (ModuleCat.of A (M ⧸ I.primaryComponent M)))).obj)) := sorry

/-- In positive degree, quotienting a module by its ideal-power-torsion primary component
induces an isomorphism on derived ideal-power-torsion cohomology over a Noetherian ring.

Noetherianity is a sufficient acyclicity hypothesis. Without an extra hypothesis, a
non-Noetherian square-zero extension gives a primary component with nonzero positive
derived torsion. -/
theorem idealCohomologyQuotientMapIsIsoOfPos [IsNoetherianRing A]
    (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{u} A) (p : ℤ) (hp : 0 < p) :
    letI : Fact I.FG := ⟨hI⟩
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat A) p).map
      (((ModuleCat.IdealPowerTorsion.derivedTorsion I ⋙
          CohomologyIn.Comparison.functor (ModuleCat.isIdealPowerTorsion I)).map
        (ModuleCat.single0Functor.map
          (ModuleCat.ofHom (Submodule.mkQ (I.primaryComponent M))))).hom)) := sorry

/-- The derived ideal-power-torsion cohomology of an ideal-power-torsion primary component
vanishes in positive degree over a Noetherian ring.

Without Noetherianity this is false in general: in the square-zero extension
`R = k[t] ⋉ (k[t,t⁻¹]/k[t])` with `I = (t)`, take the module `M = ann_R(t)`.
Its ideal-power-torsion primary component is `M` itself and has nonzero second derived
ideal-torsion. -/
theorem idealCohomologyPrimaryComponentIsZeroOfPos [IsNoetherianRing A]
    (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{u} A) (p : ℤ) (hp : 0 < p) :
    letI : Fact I.FG := ⟨hI⟩
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat A) p).obj
      (((ModuleCat.IdealPowerTorsion.derivedTorsion I ⋙
          CohomologyIn.Comparison.functor (ModuleCat.isIdealPowerTorsion I)).obj
        (ModuleCat.single0 (ModuleCat.of A (I.primaryComponent M)))).obj)) := sorry

/-- Degree-zero cohomology supported on a finitely generated ideal's vanishing locus vanishes
after quotienting a module by its ideal-power-torsion primary component. -/
theorem h0ClosedSupportQuotientPrimaryComponentIsZero (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{u} A)
    (RΓZ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓZ : IdealPowerTorsion.inclusion I ⊣ RΓZ) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
      ((RΓZ.obj
        (ModuleCat.single0 (ModuleCat.of A (M ⧸ I.primaryComponent M)))).obj)) := sorry

/-- In positive degree, quotienting a module by its ideal-power-torsion primary component
induces an isomorphism on cohomology supported on the ideal's vanishing locus. -/
theorem closedSupportCohomologyQuotientMapIsIsoOfPos (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{u} A)
    (RΓZ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓZ : IdealPowerTorsion.inclusion I ⊣ RΓZ)
    (p : ℤ) (hp : 0 < p) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat A) p).map
      ((RΓZ.map (ModuleCat.single0Functor.map
        (ModuleCat.ofHom (Submodule.mkQ (I.primaryComponent M))))).hom)) := sorry

/-- The cohomology supported on a finitely generated ideal's vanishing locus of its
ideal-power-torsion primary component vanishes in positive degree. -/
theorem closedSupportPrimaryComponentIsZeroOfPos (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{u} A)
    (RΓZ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓZ : IdealPowerTorsion.inclusion I ⊣ RΓZ)
    (p : ℤ) (hp : 0 < p) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat A) p).obj
      ((RΓZ.obj (ModuleCat.single0
        (ModuleCat.of A (I.primaryComponent M)))).obj)) := sorry

end CategoryTheory.DerivedCategory.LocalCohomology
