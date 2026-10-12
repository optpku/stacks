/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap80.Definition_80_4_1_Relative
public import stacks_project.Chap80.Lemma_80_5_1

/-!
# Algebraic spaces from étale sheaves with a smooth scheme atlas

An étale sheaf on schemes over `S` whose diagonal is representable by algebraic
spaces, and which admits a surjective smooth map from a scheme over `S`, is an
algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 80.12.3: denote the common underlying category of `Sch_fppf` and
`Sch_étale` by `Sch_α` (see Topologies, Remark 34.11.1), recovered here as the
common `Over S` of `Scheme.etaleTopology` and `Scheme.fppfTopology`. Let `S` be a
scheme. Let `F : (Over S)ᵒᵖ ⥤ Type u` be a presheaf that is a sheaf for the étale
topology, whose diagonal `diag F : F ⟶ F ⨯ F` is representable by algebraic
spaces, and that admits `U` over `S` with a map `U ⟶ F` which is surjective and
smooth. Then `F` is an algebraic space in the sense of Algebraic Spaces,
Definition 65.6.1. -/
@[stacks 07WF]
theorem IsAlgebraicSpace.of_etale_sheaf_smooth_surjective {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.etaleTopology.over S) F)
    (hΔ : representableByAlgebraicSpaces (diag F)) {U : Over S}
    (p : yoneda.obj U ⟶ F)
    (hP : (representableByAlgebraicSpaces.of_diag hΔ p).has
      (@Surjective S ⊓ @Smooth S : MorphismProperty (AlgebraicSpace S))) :
    IsAlgebraicSpace F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
