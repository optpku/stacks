/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.AlgebraicSpaceComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison from Spec to Spf for completions along a closed subset

A morphism `g : Spec(R) ⟶ X` over `S` with inverse image of `T` equal to the
closed point of `Spec(R)`, with `R` carrying its maximal-adic topology, induces
a morphism `Spf(R) ⟶ completionAlong X T` by the colimit of the sheafified
affine stages.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open AlgebraicGeometry.AlgebraicSpace TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- The morphism of presheaves from the affine stage `Spec(R ⧸ I)` into the
completion of `X` along `T`, induced by a morphism `g : Spec(R) ⟶ X` whose
inverse image of `T` is the closed point, for the maximal-adic topology on `R`. -/
def stageToCompletionAlong {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsLocalRing R] [TopologicalRing.IsWeaklyAdmissibleRing R]
    (h_adic : IsAdic (maximalIdeal R)) {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S) (X : AlgebraicSpace S)
    (T : Closeds (Points X)) (g : ofOver (Over.mk structureHom) ⟶ X)
    (hg : Points.mapOfOver g ⁻¹' (T : Set (Points X)) = {closedPoint R})
    (I : WeakIdealOfDefinition R) :
    yoneda.obj (stage R structureHom I) ⟶ completionAlong X T :=
  yonedaEquiv.symm
    ⟨yonedaEquiv (yoneda.map (stageToSpec structureHom I) ≫ g), sorry⟩

/-- The underlying map of `stageToCompletionAlong` into `X.functorOfPoints` is
`g` after `stageToSpec`. -/
theorem stageToCompletionAlong_comp_ι {R : Type u} [CommRing R]
    [TopologicalSpace R] [IsLocalRing R]
    [TopologicalRing.IsWeaklyAdmissibleRing R]
    (h_adic : IsAdic (maximalIdeal R)) {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S) (X : AlgebraicSpace S)
    (T : Closeds (Points X)) (g : ofOver (Over.mk structureHom) ⟶ X)
    (hg : Points.mapOfOver g ⁻¹' (T : Set (Points X)) = {closedPoint R})
    (I : WeakIdealOfDefinition R) :
    stageToCompletionAlong h_adic structureHom X T g hg I ≫ completionAlong.ι X T =
      yoneda.map (stageToSpec structureHom I) ≫ g :=
  sorry

/-- The morphism `Spf(R) ⟶ sheafify (completionAlong X T)` induced by a
morphism `g : Spec(R) ⟶ X` whose inverse image of `T` is the closed point,
for the maximal-adic topology on `R`. -/
def specHomToSpfHom_completionAlong {R : Type u} [CommRing R]
    [TopologicalSpace R] [IsLocalRing R]
    [TopologicalRing.IsWeaklyAdmissibleRing R]
    (h_adic : IsAdic (maximalIdeal R)) {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S) (X : AlgebraicSpace S)
    (T : Closeds (Points X)) (g : ofOver (Over.mk structureHom) ⟶ X)
    (hg : Points.mapOfOver g ⁻¹' (T : Set (Points X)) = {closedPoint R})
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    spf R structureHom ⟶
      (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).obj
        (completionAlong X T) :=
  colimit.desc
    (thickenings R structureHom ⋙ yoneda ⋙
      presheafToSheaf (Scheme.fppfTopology.over S) (Type u))
    { pt := (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).obj
        (completionAlong X T)
      ι :=
        { app I :=
            (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map
              (stageToCompletionAlong h_adic structureHom X T g hg I)
          naturality := sorry } }

/-- `specHomToSpfHom_completionAlong` restricts to the sheafified
`stageToCompletionAlong` on each affine stage. -/
theorem specHomToSpfHom_completionAlong_apply {R : Type u} [CommRing R]
    [TopologicalSpace R] [IsLocalRing R]
    [TopologicalRing.IsWeaklyAdmissibleRing R]
    (h_adic : IsAdic (maximalIdeal R)) {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S) (X : AlgebraicSpace S)
    (T : Closeds (Points X)) (g : ofOver (Over.mk structureHom) ⟶ X)
    (hg : Points.mapOfOver g ⁻¹' (T : Set (Points X)) = {closedPoint R})
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (I : WeakIdealOfDefinition R) :
    spfι R structureHom I ≫
        specHomToSpfHom_completionAlong h_adic structureHom X T g hg =
      (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map
        (stageToCompletionAlong h_adic structureHom X T g hg I) :=
  sorry

/-- Composing `specHomToSpfHom_completionAlong` with the sheafification of
`completionAlong.ι` recovers `specHomToSpfHom_algebraicSpace`. -/
theorem specHomToSpfHom_completionAlong_comp_ι {R : Type u} [CommRing R]
    [TopologicalSpace R] [IsLocalRing R]
    [TopologicalRing.IsWeaklyAdmissibleRing R]
    (h_adic : IsAdic (maximalIdeal R)) {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S) (X : AlgebraicSpace S)
    (T : Closeds (Points X)) (g : ofOver (Over.mk structureHom) ⟶ X)
    (hg : Points.mapOfOver g ⁻¹' (T : Set (Points X)) = {closedPoint R})
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    specHomToSpfHom_completionAlong h_adic structureHom X T g hg ≫
        (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map
          (completionAlong.ι X T) =
      specHomToSpfHom_algebraicSpace structureHom X g :=
  sorry

/-- For a complete local Noetherian ring with its maximal-adic topology, the
canonical morphism to the completion along a closed subset with quasi-compact
open complement is representable by algebraic spaces. -/
theorem representableByAlgebraicSpaces_specHomToSpfHom_completionAlong
    {R : Type u} [CommRing R] [TopologicalSpace R] [IsNoetherianRing R]
    [IsCompleteLocalRing R] [TopologicalRing.IsWeaklyAdmissibleRing R]
    (h_adic : IsAdic (maximalIdeal R)) {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (X : AlgebraicSpace S) (T : Closeds (Points X))
    [AlgebraicSpace.QuasiCompact (OpenSubspace.Construction.ι X T.compl)]
    (g : ofOver (Over.mk structureHom) ⟶ X)
    (hg : Points.mapOfOver g ⁻¹' (T : Set (Points X)) = {closedPoint R}) :
    AlgebraicSpace.representableByAlgebraicSpaces
      ((sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
        (specHomToSpfHom_completionAlong h_adic structureHom X T g hg)) :=
  sorry

/-- For a complete local Noetherian `S`-algebra with its maximal-adic topology,
an adic morphism from its formal spectrum to the completion of an algebraic
space along a closed subset with quasi-compact open complement comes from a
unique algebraic-space morphism whose inverse image of that subset is the
closed point. -/
@[stacks 0GBU]
theorem existsUnique_specHom_of_adicSpfHom {R : Type u} [CommRing R]
    [TopologicalSpace R] [IsNoetherianRing R] [IsCompleteLocalRing R]
    [TopologicalRing.IsWeaklyAdmissibleRing R]
    (h_adic : IsAdic (maximalIdeal R)) {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (X : AlgebraicSpace S) (T : Closeds (Points X))
    [AlgebraicSpace.QuasiCompact (OpenSubspace.Construction.ι X T.compl)]
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
