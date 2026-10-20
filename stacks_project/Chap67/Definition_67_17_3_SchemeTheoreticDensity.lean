module

public import stacks_project.Chap67.Lemma_67_17_2_SchemeTheoreticDensity

/-!
# Scheme-theoretic density of open immersions of algebraic spaces

An open immersion of algebraic spaces is scheme-theoretically dense when it
satisfies the étale-local tests of Lemma 67.17.2: every étale preimage
inclusion is scheme-theoretically dominant, equivalently some surjective étale
scheme atlas has this property.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticallyDense :
  ∀ {S : Scheme.{u}} {X U : AlgebraicSpace S} (ι : U ⟶ X) [IsOpenImmersion ι], Prop)

#check (AlgebraicGeometry.AlgebraicSpace.isSchemeTheoreticallyDense_iff :
  ∀ {S : Scheme.{u}} {X U : AlgebraicSpace S} (ι : U ⟶ X) [IsOpenImmersion ι],
    IsSchemeTheoreticallyDense ι ↔ SchemeTheoreticDensity.forallEtale ι)

#check (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticallyDense.id :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}, IsSchemeTheoreticallyDense (𝟙 X))

#check (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticallyDense.of_isIso :
  ∀ {S : Scheme.{u}} {X U : AlgebraicSpace S} (ι : U ⟶ X)
    [IsOpenImmersion ι] [IsIso ι], IsSchemeTheoreticallyDense ι)

#check (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticallyDense.of :
  ∀ {S : Scheme.{u}} {X U : AlgebraicSpace S} {ι : U ⟶ X}
    [IsOpenImmersion ι], SchemeTheoreticDensity.forallEtale ι →
      IsSchemeTheoreticallyDense ι)

#check (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticallyDense.spec :
  ∀ {S : Scheme.{u}} {X U : AlgebraicSpace S} (ι : U ⟶ X)
    [IsOpenImmersion ι] [IsSchemeTheoreticallyDense ι],
    SchemeTheoreticDensity.forallEtale ι)

#check (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticallyDense.forallEtale :
  ∀ {S : Scheme.{u}} {X U : AlgebraicSpace S} {ι : U ⟶ X}
    [IsOpenImmersion ι] [IsSchemeTheoreticallyDense ι],
    SchemeTheoreticDensity.forallEtale ι)

#check (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticallyDense.iff_existsSurjectiveEtale :
  ∀ {S : Scheme.{u}} {X U : AlgebraicSpace S} (ι : U ⟶ X) [IsOpenImmersion ι],
    IsSchemeTheoreticallyDense ι ↔ SchemeTheoreticDensity.existsSurjectiveEtale ι)

end AlgebraicGeometry.AlgebraicSpace
