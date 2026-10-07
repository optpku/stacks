module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap76.Lemma_76_45_2_Characterization

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/-- Lemma 76.45.2: let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S` which is locally of finite type. Let `m : ℤ`. Let `E` be an object of
`D_QCoh(𝒪_X)`. With notation as in Remark 76.45.1, the following are equivalent: for
every étale scheme square over `f`, the restriction `E|_U` is `m`-pseudo-coherent
relative to `V`; for some such square with `U ⟶ X` surjective, `E|_U` is
`m`-pseudo-coherent relative to `V`; and for every such square with `U` and `V`
affine, `RΓ(U, E)` is `m`-pseudo-coherent relative to `𝒪_Y(V)` as a complex of
`𝒪_X(U)`-modules. -/
@[stacks 0CSX]
theorem IsMPseudoCoherentOver.tfae {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] {E : ModuleDerived X}
    (hE : derivedQuasiCoherentModuleProperty X E) (m : ℤ) :
    List.TFAE [IsMPseudoCoherentOver.everyEtaleSquare f E m,
      IsMPseudoCoherentOver.existsSurjectiveEtaleSquare f E m,
      IsMPseudoCoherentOver.everyAffineSections f E m] :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
