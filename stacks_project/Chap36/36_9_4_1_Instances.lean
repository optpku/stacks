module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.Exact

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

variable {R : CommRingCat.{u}}

/- Compatibility checks for the canonical exactness API of affine tilde sheafification. -/
#check
  (AlgebraicGeometry.tilde.exact :
    ∀ (R : CommRingCat.{u}),
      exactFunctor (ModuleCat R) (Spec R).Modules (AlgebraicGeometry.tilde.functor R))

#check
  (inferInstance :
    (AlgebraicGeometry.tilde.functor R).PreservesZeroMorphisms)

#check
  (inferInstance : (AlgebraicGeometry.tilde.functor R).Additive)

#check
  (AlgebraicGeometry.tilde.preservesFiniteLimits R :
    PreservesFiniteLimits (AlgebraicGeometry.tilde.functor R))

#check
  (AlgebraicGeometry.tilde.preservesFiniteColimits R :
    PreservesFiniteColimits (AlgebraicGeometry.tilde.functor R))

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.Koszul

/-- Affine tilde sheafification over a commutative ring is additive. -/
noncomputable instance tildeAdditive {A : Type u} [CommRing A] :
    (AlgebraicGeometry.tilde.functor (CommRingCat.of A)).Additive :=
  let hTildeLeft :
      (AlgebraicGeometry.tilde.functor (CommRingCat.of A)).IsLeftAdjoint :=
    (AlgebraicGeometry.tilde.adjunction (R := CommRingCat.of A)).isLeftAdjoint
  let hTildeZero :
      (AlgebraicGeometry.tilde.functor (CommRingCat.of A)).PreservesZeroMorphisms :=
    @Functor.preservesZeroMorphisms_of_isLeftAdjoint _ _ _ _ _ _
      (AlgebraicGeometry.tilde.functor (CommRingCat.of A)) hTildeLeft
  let hTildeCoproducts :
      PreservesColimitsOfShape (Discrete WalkingPair)
        (AlgebraicGeometry.tilde.functor (CommRingCat.of A)) :=
    (AlgebraicGeometry.tilde.adjunction
      (R := CommRingCat.of A)).leftAdjoint_preservesColimits.preservesColimitsOfShape
  let hTildeBiproducts :
      PreservesBinaryBiproducts
        (AlgebraicGeometry.tilde.functor (CommRingCat.of A)) :=
    @preservesBinaryBiproducts_of_preservesBinaryCoproducts
      _ _ _ _ _ _ (AlgebraicGeometry.tilde.functor (CommRingCat.of A))
        hTildeZero hTildeCoproducts
  @Functor.additive_of_preservesBinaryBiproducts
    _ _ _ _ _ _ (AlgebraicGeometry.tilde.functor (CommRingCat.of A))
      inferInstance hTildeZero hTildeBiproducts

/-- Affine tilde sheafification over a commutative ring preserves finite limits. -/
noncomputable instance tildePreservesFiniteLimits {A : Type u} [CommRing A] :
    PreservesFiniteLimits (AlgebraicGeometry.tilde.functor (CommRingCat.of A)) :=
  AlgebraicGeometry.tilde.preservesFiniteLimits (CommRingCat.of A)

/-- Affine tilde sheafification over a commutative ring preserves finite colimits. -/
noncomputable instance tildePreservesFiniteColimits {A : Type u} [CommRing A] :
    PreservesFiniteColimits (AlgebraicGeometry.tilde.functor (CommRingCat.of A)) :=
  AlgebraicGeometry.tilde.preservesFiniteColimits (CommRingCat.of A)

end AlgebraicGeometry.RingedSpace.ModuleDerived.Koszul

end
