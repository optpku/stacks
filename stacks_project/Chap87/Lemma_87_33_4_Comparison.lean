/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import ReasLib.RingTheory.Completion.LocalRing
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Remark_67_12_5_Opens
public import stacks_project.Chap80.Definition_80_3_1_RelativelyRepresentable
public import stacks_project.Chap87.Lemma_87_14_4_Completion
public import stacks_project.Chap87.Lemma_87_33_3_Comparison

/-!
# Comparison from Spec to Spf for completions along a closed subset

A morphism `g : Spec(R) ⟶ X` over `S` with inverse image of `T` equal to the
closed point of `Spec(R)` induces a morphism `Spf(R) ⟶ completionAlong X T`
by the colimit of the sheafified affine stages.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open AlgebraicGeometry.AlgebraicSpace TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- The morphism of presheaves from the affine stage `Spec(R ⧸ I)` into the
completion of `X` along `T`, induced by a morphism `g : Spec(R) ⟶ X` whose
inverse image of `T` is the closed point. -/
def stageToCompletionAlong {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsLocalRing R] [TopologicalRing.IsWeaklyAdmissibleRing R] {S : Scheme.{u}}
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
    [TopologicalRing.IsWeaklyAdmissibleRing R] {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S) (X : AlgebraicSpace S)
    (T : Closeds (Points X)) (g : ofOver (Over.mk structureHom) ⟶ X)
    (hg : Points.mapOfOver g ⁻¹' (T : Set (Points X)) = {closedPoint R})
    (I : WeakIdealOfDefinition R) :
    stageToCompletionAlong structureHom X T g hg I ≫ completionAlong.ι X T =
      yoneda.map (stageToSpec structureHom I) ≫ g :=
  sorry

/-- The morphism `Spf(R) ⟶ sheafify (completionAlong X T)` induced by a
morphism `g : Spec(R) ⟶ X` whose inverse image of `T` is the closed point. -/
def specHomToSpfHom_completionAlong {R : Type u} [CommRing R]
    [TopologicalSpace R] [IsLocalRing R]
    [TopologicalRing.IsWeaklyAdmissibleRing R] {S : Scheme.{u}}
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
              (stageToCompletionAlong structureHom X T g hg I)
          naturality := sorry } }

/-- `specHomToSpfHom_completionAlong` restricts to the sheafified
`stageToCompletionAlong` on each affine stage. -/
theorem specHomToSpfHom_completionAlong_apply {R : Type u} [CommRing R]
    [TopologicalSpace R] [IsLocalRing R]
    [TopologicalRing.IsWeaklyAdmissibleRing R] {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S) (X : AlgebraicSpace S)
    (T : Closeds (Points X)) (g : ofOver (Over.mk structureHom) ⟶ X)
    (hg : Points.mapOfOver g ⁻¹' (T : Set (Points X)) = {closedPoint R})
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (I : WeakIdealOfDefinition R) :
    spfι R structureHom I ≫
        specHomToSpfHom_completionAlong structureHom X T g hg =
      (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map
        (stageToCompletionAlong structureHom X T g hg I) :=
  sorry

/-- Composing `specHomToSpfHom_completionAlong` with the sheafification of
`completionAlong.ι` recovers `specHomToSpfHom_algebraicSpace`. -/
theorem specHomToSpfHom_completionAlong_comp_ι {R : Type u} [CommRing R]
    [TopologicalSpace R] [IsLocalRing R]
    [TopologicalRing.IsWeaklyAdmissibleRing R] {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S) (X : AlgebraicSpace S)
    (T : Closeds (Points X)) (g : ofOver (Over.mk structureHom) ⟶ X)
    (hg : Points.mapOfOver g ⁻¹' (T : Set (Points X)) = {closedPoint R})
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    specHomToSpfHom_completionAlong structureHom X T g hg ≫
        (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map
          (completionAlong.ι X T) =
      specHomToSpfHom_algebraicSpace structureHom X g :=
  sorry

/-- The morphism `specHomToSpfHom_completionAlong` is representable by algebraic
spaces, i.e. adic in the sense of Definition 87.23.2 once
`completionAlong X T` is locally adic*. -/
theorem representableByAlgebraicSpaces_specHomToSpfHom_completionAlong
    {R : Type u} [CommRing R] [TopologicalSpace R] [IsNoetherianRing R]
    [IsCompleteLocalRing R] [TopologicalRing.IsWeaklyAdmissibleRing R]
    (h_adic : IsAdic (maximalIdeal R)) {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (X : AlgebraicSpace S) (T : Closeds (Points X))
    [AlgebraicSpace.QuasiCompact (OpenSubspace.ofOpensι T.compl)]
    (g : ofOver (Over.mk structureHom) ⟶ X)
    (hg : Points.mapOfOver g ⁻¹' (T : Set (Points X)) = {closedPoint R}) :
    AlgebraicSpace.representableByAlgebraicSpaces
      ((sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
        (specHomToSpfHom_completionAlong structureHom X T g hg)) :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
