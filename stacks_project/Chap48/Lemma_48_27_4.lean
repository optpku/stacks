module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.PerfectPairing

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 48.27.4
For a proper morphism `f : X ⟶ Spec k` and a perfect complex `E` on `X`, the trace pairing
`Hⁱ(X, ω_X ⊗ᴸ Eᵛ) × H⁻ⁱ(X, E) ⟶ k` given by `t((1_ω ⊗ ε)(ξ ∪ η))` is perfect in every
degree `i`. -/
@[stacks 0FVY]
#check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.pairingWith_isPerfPair_of_perfect :
  {k : Type u} → [Field k] → {X : Scheme.{u}} →
  [MonoidalCategory (AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace)] →
  [BraidedCategory (AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace)] →
  [MonoidalClosed (AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace)] →
  (e : AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.fieldObject k ≅
    ModuleCat.of k k) →
  (f : X ⟶ Spec (CommRingCat.of k)) → [IsProper f] →
  (E : @AlgebraicGeometry.RingedSpace.ModuleDerived.Perfect X.toRingedSpace) →
  (i : ℤ) →
  LinearMap.IsPerfPair
    (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.perfectPairingWith e f E i))
