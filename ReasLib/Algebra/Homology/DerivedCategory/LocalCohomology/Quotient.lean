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
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
      (((ModuleCat.IdealPowerTorsion.derivedTorsion I ⋙
          CohomologyIn.Comparison.functor (ModuleCat.isIdealPowerTorsion I)).obj
        (ModuleCat.single0 (ModuleCat.of A (M ⧸ I.primaryComponent M)))).obj)) := sorry

/-- In positive degree, quotienting a module by its ideal-power-torsion primary component
induces an isomorphism on derived ideal-power-torsion cohomology. -/
theorem idealCohomologyQuotientMapIsIsoOfPos (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{u} A) (p : ℤ) (hp : 0 < p) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat A) p).map
      (((ModuleCat.IdealPowerTorsion.derivedTorsion I ⋙
          CohomologyIn.Comparison.functor (ModuleCat.isIdealPowerTorsion I)).map
        (ModuleCat.single0Functor.map
          (ModuleCat.ofHom (Submodule.mkQ (I.primaryComponent M))))).hom)) := sorry

/-- The derived ideal-power-torsion cohomology of an ideal-power-torsion primary component
vanishes in positive degree. -/
theorem idealCohomologyPrimaryComponentIsZeroOfPos (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{u} A) (p : ℤ) (hp : 0 < p) :
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
