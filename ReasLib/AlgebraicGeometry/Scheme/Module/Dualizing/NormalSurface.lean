module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DualizingModule
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Koszul.PrincipalOpen
public import ReasLib.AlgebraicGeometry.Scheme.Module.Dualizing
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Modification
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Normal.Connected
public import ReasLib.RingTheory.Normal.Local
public import Mathlib.RingTheory.KrullDimension.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace.ModuleDerived.Koszul
open AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IsDualizingModule

/-- On an integral Noetherian normal surface, dualizing complexes exist exactly
when dualizing modules exist. -/
theorem existsComplex_iff_exists_of_normalSurface
    (X : Scheme.{u}) [IsNoetherian X] [AlgebraicGeometry.IsIntegral X]
    (h_normal : X.isNormal) (h_dimension : topologicalKrullDim X = 2) :
    (∃ K : RingedSpace.ModuleDerived X.toRingedSpace, Scheme.IsDualizingComplex K) ↔
      ∃ ωX : X.Modules, Scheme.IsDualizingModule ωX := sorry

/-- A normal modification of the spectrum of a two-dimensional Noetherian normal
local domain carries a dualizing module whenever the base does. -/
theorem exists_on_normalModification
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsNormalRing A]
    (h_dimension : ringKrullDim A = 2)
    (ωA : ModuleCat.{u} A) (hωA : ModuleCat.IsDualizingModule ωA)
    {X : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ Spec (.of A)) [AlgebraicGeometry.IsModification f]
    (h_normal : X.isNormal) :
    ∃ ωX : X.Modules, Scheme.IsDualizingModule ωX := sorry

/-- A dualizing module on a normal modification can be chosen so that its shift
by `2` is properly normalized relative to the affine image of the shifted base module. -/
theorem exists_normalizedRelativeTo
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsNormalRing A]
    (h_dimension : ringKrullDim A = 2)
    (ωA : ModuleCat.{u} A) (hωA : ModuleCat.IsDualizingModule ωA)
    {X : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ Spec (.of A)) [AlgebraicGeometry.IsModification f]
    (h_normal : X.isNormal) :
    let ωS := (affineDerivedTilde A).obj ((ModuleCat.single0 ωA)⟦(2 : ℤ)⟧)
    ∃ ωX : X.Modules,
      Scheme.IsDualizingModule ωX ∧
        ProperRelativeTo f ωS
          (((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧) := sorry

end AlgebraicGeometry.Scheme.IsDualizingModule
