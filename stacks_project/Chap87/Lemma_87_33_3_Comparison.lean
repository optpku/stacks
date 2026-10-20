/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import ReasLib.AlgebraicGeometry.FormalSpectrum.AlgebraicSpaceComparison

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

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.specHomToSpfHom_algebraicSpace :
  ∀ {R : Type u} [CommRing R] [TopologicalSpace R]
    [TopologicalRing.IsWeaklyAdmissibleRing R] {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S) (X : AlgebraicSpace S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)],
    (AlgebraicSpace.ofOver (Over.mk structureHom) ⟶ X) →
      (spf R structureHom ⟶
        (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).obj
          X.functorOfPoints))

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.specHomToSpfHom_algebraicSpace_apply :
  ∀ {R : Type u} [CommRing R]
    [TopologicalSpace R] [TopologicalRing.IsWeaklyAdmissibleRing R]
    {S : Scheme.{u}} (structureHom : Spec (.of R) ⟶ S) (X : AlgebraicSpace S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (f : AlgebraicSpace.ofOver (Over.mk structureHom) ⟶ X),
    specHomToSpfHom_algebraicSpace structureHom X f =
      spfToSpec structureHom ≫
        (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map f)

end AlgebraicGeometry.AffineFormalAlgebraicSpace
