module

public import stacks_project.Chap57.Definition_57_15_1_Kernel

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- Derived pullback of a perfect kernel along the product comparison
`X₁ ×_{S'} Y₁ ⟶ X ×_S Y`. -/
noncomputable def FourierMukaiObject.modulePullbackKernel
    {S S' : Scheme.{u}} (g : S' ⟶ S) {X Y : FourierMukaiObject S}
    (K : @RingedSpace.ModuleDerived.Perfect
      (Limits.pullback X.hom Y.hom).toRingedSpace) :=
  (RingedSpace.modulePullbackPerfect
      ((FourierMukaiObject.productComparison g X Y).toLRSHom.toShHom)).obj K

/-- Lemma 57.15.3: if `K` is the Fourier--Mukai kernel of a relative
equivalence from `X` to `Y` over `S`, and `g : S' ⟶ S` is a morphism of
schemes, then the derived pullback of `K` along the product comparison
`X₁ ×_{S'} Y₁ ⟶ X ×_S Y`, with `X₁ = S' ×_S X` and `Y₁ = S' ×_S Y`, is
the Fourier--Mukai kernel of a relative equivalence from `X₁` to `Y₁`
over `S'`. -/
@[stacks 0G0K]
instance FourierMukaiObject.instIsRelativeEquivalenceKernel_modulePullback
    {S S' : Scheme.{u}} (g : S' ⟶ S) {X Y : FourierMukaiObject S}
    (K : @RingedSpace.ModuleDerived.Perfect
      (Limits.pullback X.hom Y.hom).toRingedSpace)
    [FourierMukaiObject.IsRelativeEquivalenceKernel K] :
    FourierMukaiObject.IsRelativeEquivalenceKernel
      (FourierMukaiObject.modulePullbackKernel g K) :=
  sorry

/-- Object-level derived pullback of a perfect kernel is the representative of
`mapKernel` of its isomorphism class. -/
theorem FourierMukaiObject.modulePullbackKernel_mk_eq_mapKernel
    {S S' : Scheme.{u}} (g : S' ⟶ S) {X Y : FourierMukaiObject S}
    (K : @RingedSpace.ModuleDerived.Perfect
      (Limits.pullback X.hom Y.hom).toRingedSpace) :
    Quotient.mk'' (FourierMukaiObject.modulePullbackKernel g K) =
      FourierMukaiObject.mapKernel g X Y (Quotient.mk'' K) :=
  sorry
