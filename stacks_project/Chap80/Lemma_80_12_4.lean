module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap80.Definition_80_4_1_Relative

/-!
# Algebraic spaces from étale sheaves with an algebraic-space smooth atlas

An étale sheaf on schemes over `S` that admits a representable, surjective, and
smooth map from an algebraic space is itself an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 80.12.4: denote the common underlying category of `Sch_fppf` and
`Sch_étale` by `Sch_α` (see Topologies, Remark 34.11.1), recovered here as the
common `Over S` of `Scheme.etaleTopology` and `Scheme.fppfTopology`. Let `S` be a
scheme. Let `F : (Over S)ᵒᵖ ⥤ Type u` be a presheaf. If `F` is a sheaf for the
étale topology, and there is an algebraic space `U` over `S` with a map `U ⟶ F`
which is representable by algebraic spaces, surjective, and smooth, then `F` is
an algebraic space in the sense of Algebraic Spaces, Definition 65.6.1. -/
@[stacks 0GE0]
theorem IsAlgebraicSpace.of_etaleSheaf_smooth_surjective {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.etaleTopology.over S) F)
    {U : (Over S)ᵒᵖ ⥤ Type u} [IsAlgebraicSpace U] (a : U ⟶ F)
    (ha : relativeAlgebraicSpaces
      (@Surjective S ⊓ @Smooth S : MorphismProperty (AlgebraicSpace S)) a) :
    IsAlgebraicSpace F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
