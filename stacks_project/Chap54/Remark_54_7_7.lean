module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DualizingModule
public import ReasLib.AlgebraicGeometry.Scheme.Module.Dualizing.NormalSurface
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Remark 54.7.7 (1): An integral Noetherian normal scheme of dimension `2` has a
dualizing complex if and only if it has a dualizing module. -/
@[stacks 0B4R] #check
  (AlgebraicGeometry.Scheme.IsDualizingModule.existsComplex_iff_exists_of_normalSurface :
    ∀ (X : Scheme.{u}) [IsNoetherian X] [AlgebraicGeometry.IsIntegral X],
      (h_normal : X.isNormal) → (h_dimension : topologicalKrullDim X = 2) →
      (∃ K : RingedSpace.ModuleDerived X.toRingedSpace,
        Scheme.IsDualizingComplex K) ↔
        ∃ ωX : X.Modules, Scheme.IsDualizingModule ωX)

/- Remark 54.7.7 (2): A two-dimensional Noetherian normal local domain has a dualizing
complex if and only if it has a dualizing module. -/
@[stacks 0B4R] #check
  (ModuleCat.IsDualizingModule.existsComplex_iff_exists_of_normalLocalDomain :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsNormalRing A],
      (h_dimension : ringKrullDim A = 2) →
      (∃ K : DerivedCategory (ModuleCat.{u} A), DerivedCategory.IsDualizing K) ↔
        ∃ ωA : ModuleCat.{u} A, ModuleCat.IsDualizingModule ωA)

/- Remark 54.7.7 (3): A normal modification of the spectrum of a two-dimensional
Noetherian normal local domain with a dualizing module has a dualizing module. -/
@[stacks 0B4R] #check
  (AlgebraicGeometry.Scheme.IsDualizingModule.exists_on_normalModification :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsNormalRing A],
      ringKrullDim A = 2 →
      (ωA : ModuleCat.{u} A) → ModuleCat.IsDualizingModule ωA →
      ∀ {X : Scheme.{u}} [IsNoetherian X],
        (f : X ⟶ Spec (.of A)) → [AlgebraicGeometry.IsModification f] →
        X.isNormal → ∃ ωX : X.Modules, Scheme.IsDualizingModule ωX)

/- Remark 54.7.7 (4): The dualizing module on a normal modification can be chosen so
that its shift by `2` is normalized relative to the affine image of the base dualizing module. -/
@[stacks 0B4R] #check
  (AlgebraicGeometry.Scheme.IsDualizingModule.exists_normalizedRelativeTo :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsNormalRing A],
      ringKrullDim A = 2 →
      (ωA : ModuleCat.{u} A) → ModuleCat.IsDualizingModule ωA →
      ∀ {X : Scheme.{u}} [IsNoetherian X],
        (f : X ⟶ Spec (.of A)) → [AlgebraicGeometry.IsModification f] → X.isNormal →
        let ωS :=
          (AlgebraicGeometry.RingedSpace.ModuleDerived.Koszul.affineDerivedTilde A).obj
            ((ModuleCat.single0 ωA)⟦(2 : ℤ)⟧)
        ∃ ωX : X.Modules,
          Scheme.IsDualizingModule ωX ∧
            AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex.ProperRelativeTo f ωS
              (((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧))
