/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap80.Definition_80_4_1_Relative
public import stacks_project.Chap80.Lemma_80_5_1

/-!
# Bootstrap of algebraic spaces from an étale algebraic-space atlas

An fppf sheaf on schemes over `S` that admits an étale surjective map from an
algebraic space is itself an algebraic space, either assuming representability
of the diagonal by algebraic spaces, or assuming that the atlas map is
representable by algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Theorem 80.6.1 (1): let `S` be a scheme. Let `F : (Over S)ᵒᵖ ⥤ Type u` be a
functor. If `F` is a sheaf for the fppf topology, the diagonal
`diag F : F ⟶ F ⨯ F` is representable by algebraic spaces, and there is an
algebraic space `X` with a map `X ⟶ F` which is surjective and étale, then `F`
is an algebraic space. -/
@[stacks 03Y3]
theorem IsAlgebraicSpace.of_diag_etale_surjective {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (hΔ : representableByAlgebraicSpaces (diag F))
    {X : (Over S)ᵒᵖ ⥤ Type u} [IsAlgebraicSpace X] (a : X ⟶ F)
    (hP : (representableByAlgebraicSpaces.of_diag_isAlgebraicSpace hΔ a).has
      (@Surjective S ⊓ @Etale S : MorphismProperty (AlgebraicSpace S))) :
    IsAlgebraicSpace F :=
  sorry

/-- Theorem 80.6.1 (2): let `S` be a scheme. Let `F : (Over S)ᵒᵖ ⥤ Type u` be a
functor. If `F` is a sheaf for the fppf topology, and there is an algebraic
space `X` with a map `X ⟶ F` which is representable by algebraic spaces,
surjective, and étale, then `F` is an algebraic space. -/
@[stacks 03Y3]
theorem IsAlgebraicSpace.of_etale_surjective {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    {X : (Over S)ᵒᵖ ⥤ Type u} [IsAlgebraicSpace X] (a : X ⟶ F)
    (ha : relativeAlgebraicSpaces
      (@Surjective S ⊓ @Etale S : MorphismProperty (AlgebraicSpace S)) a) :
    IsAlgebraicSpace F :=
  sorry

/-- If the diagonal of a presheaf is representable by algebraic spaces, then an
étale surjective map from an algebraic space is representable by algebraic
spaces with those properties in the sense of `relativeAlgebraicSpaces`. -/
theorem relativeAlgebraicSpaces.etale_surjective_of_diag {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (hΔ : representableByAlgebraicSpaces (diag F))
    {X : (Over S)ᵒᵖ ⥤ Type u} [IsAlgebraicSpace X] (a : X ⟶ F)
    (hP : (representableByAlgebraicSpaces.of_diag_isAlgebraicSpace hΔ a).has
      (@Surjective S ⊓ @Etale S : MorphismProperty (AlgebraicSpace S))) :
    relativeAlgebraicSpaces
      (@Surjective S ⊓ @Etale S : MorphismProperty (AlgebraicSpace S)) a :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
