module

public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap83.Definition_83_5_18_OrbitSpace
public import stacks_project.Chap83.Lemma_83_5_20_OrbitMap

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

/-- Lemma 83.5.20: Let `B ⟶ S` as in Section 83.2. Let `j = (t, s) : R ⟶ U ⨯ U` be a
pre-relation. Assume `R` and `U` are locally of finite type over `B`. Let `φ : U ⟶ X` be an
`R`-invariant morphism of algebraic spaces over `B`. Then `φ` is an orbit space for `R` if and
only if, for every geometric point `kbar` of `B`, the natural map
`Quot (P.weaklyEquivalent (Over.mk kbar.hom)) ⟶ (Over.mk kbar.hom ⟶ X)` is bijective. -/
@[stacks 04A0]
theorem isOrbitSpace_iff_bijective_weaklyEquivalentQuotMap
    {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B} (P : PreRelation U)
    {φ : U ⟶ X} (hφ : P.IsInvariant φ)
    [LocallyOfFiniteType U.hom] [LocallyOfFiniteType P.left.hom] :
    P.IsOrbitSpace φ ↔
      ∀ kbar : GeometricPoint B, Function.Bijective (P.weaklyEquivalentQuotMap hφ kbar) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.PreRelation
