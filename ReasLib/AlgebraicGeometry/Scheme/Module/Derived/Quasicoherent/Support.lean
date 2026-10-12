/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedSubset.Derived.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Affine

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The closed subset of `Spec A` cut out by an ideal `I`. -/
def affineZeroLocus {A : CommRingCat.{u}} (I : Ideal A) :
    TopologicalSpace.Closeds (Spec A) :=
  ⟨PrimeSpectrum.zeroLocus (I : Set A), PrimeSpectrum.isClosed_zeroLocus _⟩

/-- The underlying set of `affineZeroLocus I` is the zero locus of `I`. -/
theorem coe_affineZeroLocus {A : CommRingCat.{u}} (I : Ideal A) :
    (affineZeroLocus I : Set (Spec A)) =
      PrimeSpectrum.zeroLocus (I : Set A) := sorry

namespace DerivedQCoh

/-- The derived affine tilde functor from modules to complexes with quasicoherent cohomology. -/
noncomputable abbrev affineTilde (A : CommRingCat.{u}) :
    DerivedCategory (ModuleCat A) ⥤
      DerivedCategory.CohomologyIn
        (RingedSpace.quasiCoherentModuleProperty (Spec A).toRingedSpace) :=
  (AlgebraicGeometry.tildeEquiv :
      ModuleCat A ≌ Scheme.QCoh (Spec A)).mapDerivedCategory.functor ⋙
    comparison (Spec A)

/-- The derived affine tilde functor is an equivalence. -/
noncomputable instance affineTildeIsEquivalence (A : CommRingCat.{u}) :
    Functor.IsEquivalence (affineTilde A) := sorry

/-- Derived global sections on `Spec A` supported on `V(I)`, transported to derived `A`-modules. -/
noncomputable abbrev affineGlobalSectionsWithSupport {A : CommRingCat.{u}}
    (I : Ideal A) : DerivedCategory (ModuleCat A) ⥤ DerivedCategory (ModuleCat A) :=
  affineTilde A ⋙
    (DerivedCategory.cohomologyIn
      (RingedSpace.quasiCoherentModuleProperty (Spec A).toRingedSpace)).ι ⋙
    RingedSpace.ClosedSubset.GlobalSectionsWithSupport.derived
      (Spec A).toRingedSpace (Scheme.affineZeroLocus I) ⋙
    ModuleCat.derivedRestrictionOfScalars (Scheme.ΓSpecIso A).inv.hom

end DerivedQCoh

end AlgebraicGeometry.Scheme
