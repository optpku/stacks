module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap80.Definition_80_4_1_Relative

/-!
# Precomposition cancellation of representability by algebraic spaces

If `a : F ⟶ G` is a relative fppf cover of fppf sheaves (representable by
algebraic spaces, surjective, flat, and locally of finite presentation) and
`a ≫ b` is representable by algebraic spaces, then so is `b : G ⟶ H`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 80.11.4: let `S` be a scheme. Let `a : F ⟶ G` and `b : G ⟶ H` be
transformations of functors `(Over S)ᵒᵖ ⥤ Type u` (Stacks
`(Sch/S)_fppf^opp → Sets`). Assume `F`, `G`, `H` are sheaves for the fppf
topology, `a` is representable by algebraic spaces, flat, locally of finite
presentation, and surjective, and `a ≫ b` (Stacks `b ∘ a`) is representable by
algebraic spaces. Then `b` is representable by algebraic spaces.

Testing on `ξ : yoneda.obj U ⟶ H` (Stacks `ξ ∈ H(U)`) is the existing Yoneda
unfolding of `representableByAlgebraicSpaces`. -/
@[stacks 0AMP]
theorem representableByAlgebraicSpaces.of_precomp {S : Scheme.{u}}
    {F G H : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (hG : Presheaf.IsSheaf (Scheme.fppfTopology.over S) G)
    (hH : Presheaf.IsSheaf (Scheme.fppfTopology.over S) H)
    (a : F ⟶ G) (b : G ⟶ H)
    (ha : relativeAlgebraicSpaces
      (@Surjective S ⊓ @Flat S ⊓ @LocallyOfFinitePresentation S :
        MorphismProperty (AlgebraicSpace S)) a)
    (hba : representableByAlgebraicSpaces (a ≫ b)) :
    representableByAlgebraicSpaces b :=
  sorry

/-- Representability by algebraic spaces of `b : G ⟶ H` is equivalent to that of
the composite `a ≫ b` when `a` is representable by algebraic spaces, surjective,
flat, and locally of finite presentation, for fppf sheaves `F`, `G`, `H`. The
forward direction is `of_precomp`; the reverse is composition stability. -/
theorem representableByAlgebraicSpaces.of_precomp_iff {S : Scheme.{u}}
    {F G H : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (hG : Presheaf.IsSheaf (Scheme.fppfTopology.over S) G)
    (hH : Presheaf.IsSheaf (Scheme.fppfTopology.over S) H)
    (a : F ⟶ G) (b : G ⟶ H)
    (ha : relativeAlgebraicSpaces
      (@Surjective S ⊓ @Flat S ⊓ @LocallyOfFinitePresentation S :
        MorphismProperty (AlgebraicSpace S)) a) :
    representableByAlgebraicSpaces (a ≫ b) ↔ representableByAlgebraicSpaces b :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
