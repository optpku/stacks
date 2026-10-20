module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.EtaleLocal
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 75.5.2: let `S` be a scheme. Let `X` be an algebraic space over `S`. Let `E`
be an object of `D(𝒪_X)`. The following are equivalent: `E` is in `D_QCoh(𝒪_X)`; for
every étale morphism `φ : U ⟶ X` where `U` is an affine scheme, `φ* E` is in
`D_QCoh(𝒪_U)`; for every étale morphism `φ : U ⟶ X` where `U` is a scheme, `φ* E` is
in `D_QCoh(𝒪_U)`; there exists a surjective étale morphism `φ : U ⟶ X` where `U` is a
scheme such that `φ* E` is in `D_QCoh(𝒪_U)`; and there exists a surjective étale
morphism of algebraic spaces `f : Y ⟶ X` such that `Lf* E` is in `D_QCoh(𝒪_Y)`. -/
@[stacks 08F2] #check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.tfae :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (E : ModuleDerived X),
    List.TFAE [derivedQuasiCoherentModuleProperty X E, DerivedQCoh.forallAffine E,
      DerivedQCoh.forallScheme E, DerivedQCoh.existsScheme E, DerivedQCoh.existsEtale E])
