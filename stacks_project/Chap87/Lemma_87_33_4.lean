module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import ReasLib.RingTheory.Completion.LocalRing
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Remark_67_12_5_Opens
public import stacks_project.Chap87.Lemma_87_33_4_Comparison

/-!
# Maps out of affine formal schemes into a completion along a closed subset

For a complete local Noetherian `S`-algebra `R` and an algebraic space `X`
over `S`, an adic morphism `Spf(R) ⟶ X_/T` corresponds to a unique morphism
`Spec(R) ⟶ X` whose inverse image of `T` is the closed point of `Spec(R)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing
open AlgebraicGeometry.AlgebraicSpace TopologicalSpace
open AlgebraicGeometry.AffineFormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- Lemma 87.33.4: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
Let `T ⊆ Points X` be a closed subset such that the open immersion
`OpenSubspace.ofOpensι T.compl` of `X \ T` into `X` is quasi-compact. Let `R`
be a complete local Noetherian `S`-algebra. Then an adic morphism
`p : spf R structureHom ⟶ sheafify (completionAlong X T)` corresponds to a
unique morphism `g : Spec(R) ⟶ X` such that
`Points.mapOfOver g ⁻¹' T = {closedPoint R}`.

Adicness is `AlgebraicSpace.representableByAlgebraicSpaces` on the underlying
presheaf morphism, which is the condition of Definition 87.23.2 once
Lemma 87.20.8 makes `completionAlong X T` locally adic*. -/
@[stacks 0GBU]
theorem existsUnique_specHom_of_adicSpfHom {R : Type u} [CommRing R]
    [TopologicalSpace R] [IsNoetherianRing R] [IsCompleteLocalRing R]
    [TopologicalRing.IsWeaklyAdmissibleRing R]
    (h_adic : IsAdic (maximalIdeal R)) {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (X : AlgebraicSpace S) (T : Closeds (Points X))
    [AlgebraicSpace.QuasiCompact (OpenSubspace.ofOpensι T.compl)]
    (p : spf R structureHom ⟶
      (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).obj
        (completionAlong X T))
    (hp : AlgebraicSpace.representableByAlgebraicSpaces
      ((sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map p)) :
    ∃! g : ofOver (Over.mk structureHom) ⟶ X,
      Points.mapOfOver g ⁻¹' (T : Set (Points X)) = {closedPoint R} ∧
        specHomToSpfHom_algebraicSpace structureHom X g =
          p ≫ (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map
            (completionAlong.ι X T) :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
