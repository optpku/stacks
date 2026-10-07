module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.SerrePairing

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Remark 48.27.6
For a proper Cohen–Macaulay equidimensional scheme `X` over a field `k` of dimension `d`,
and a finite locally free `O_X`-module `E` with dual `Eᵛ`, the pairing
`Hⁱ(X, ω_X ⊗ Eᵛ) × Hᵈ⁻ⁱ(X, E) ⟶ k` given by `t((1 ⊗ ε)(ξ ∪ η))` is perfect. -/
@[stacks 0FW0]
#check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.serrePairingWith_isPerfPair :
  {k : Type u} → [Field k] → {X : Scheme.{u}} →
  [MonoidalCategory (AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace)] →
  [BraidedCategory (AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace)] →
  [MonoidalClosed (AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace)] →
  (e : AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.fieldObject k ≅
    ModuleCat.of k k) →
  (f : X ⟶ Spec (CommRingCat.of k)) → [IsProper f] →
  [AlgebraicGeometry.Scheme.CohenMacaulay X] → [TopologicalSpace.EquidimensionalSpace X] →
  (d : ℕ) → (h_dimension : topologicalKrullDim X = d) →
  (E : ObjectProperty.FullSubcategory
    (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) →
  (i : ℤ) →
  LinearMap.IsPerfPair
    (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.serrePairingWith
      e f d h_dimension E i))
