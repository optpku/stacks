module

public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap87.Lemma_87_33_1_Comparison

/-!
# Comparison from Spec to Spf for algebraic-space targets

Precomposition with `spfToSpec` yields the natural map
`Mor_S(Spec(R), X) → Mor_S(Spf(R), X)` when `X` is an algebraic space over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- The natural map `Mor_S(Spec(R), X) → Mor_S(Spf(R), X)` induced by
precomposition with `spfToSpec`, for an algebraic space `X` over `S`. -/
def specHomToSpfHom_algebraicSpace {R : Type u} [CommRing R] [TopologicalSpace R]
    [TopologicalRing.IsWeaklyAdmissibleRing R] {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S) (X : AlgebraicSpace S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    (AlgebraicSpace.ofOver (Over.mk structureHom) ⟶ X) →
      (spf R structureHom ⟶
        (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).obj
          X.functorOfPoints) :=
  fun f ↦
    spfToSpec structureHom ≫
      (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map f

/-- `specHomToSpfHom_algebraicSpace` is precomposition with `spfToSpec` after
sheafifying the algebraic-space morphism. -/
theorem specHomToSpfHom_algebraicSpace_apply {R : Type u} [CommRing R]
    [TopologicalSpace R] [TopologicalRing.IsWeaklyAdmissibleRing R]
    {S : Scheme.{u}} (structureHom : Spec (.of R) ⟶ S) (X : AlgebraicSpace S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (f : AlgebraicSpace.ofOver (Over.mk structureHom) ⟶ X) :
    specHomToSpfHom_algebraicSpace structureHom X f =
      spfToSpec structureHom ≫
        (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map f :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
