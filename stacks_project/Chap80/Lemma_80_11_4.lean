/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Cancellation
import StacksCheckRecall

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

/- Lemma 80.11.4: let `S` be a scheme. Let `a : F ⟶ G` and `b : G ⟶ H` be
transformations of functors `(Over S)ᵒᵖ ⥤ Type u` (Stacks
`(Sch/S)_fppf^opp → Sets`). Assume `F`, `G`, `H` are sheaves for the fppf
topology, `a` is representable by algebraic spaces, flat, locally of finite
presentation, and surjective, and `a ≫ b` (Stacks `b ∘ a`) is representable by
algebraic spaces. Then `b` is representable by algebraic spaces.

Testing on `ξ : yoneda.obj U ⟶ H` (Stacks `ξ ∈ H(U)`) is the existing Yoneda
unfolding of `representableByAlgebraicSpaces`. -/
@[stacks 0AMP] #check
  (AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces.of_precomp :
    ∀ {S : Scheme.{u}}
    {F G H : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (hG : Presheaf.IsSheaf (Scheme.fppfTopology.over S) G)
    (hH : Presheaf.IsSheaf (Scheme.fppfTopology.over S) H)
    (a : F ⟶ G) (b : G ⟶ H)
    (ha : relativeAlgebraicSpaces
      (@Surjective S ⊓ @Flat S ⊓ @LocallyOfFinitePresentation S :
        MorphismProperty (AlgebraicSpace S)) a)
    (hba : representableByAlgebraicSpaces (a ≫ b)),
    representableByAlgebraicSpaces b)

/- Representability by algebraic spaces of `b : G ⟶ H` is equivalent to that of
the composite `a ≫ b` when `a` is representable by algebraic spaces, surjective,
flat, and locally of finite presentation, for fppf sheaves `F`, `G`, `H`. The
forward direction is `of_precomp`; the reverse is composition stability. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces.of_precomp_iff :
    ∀ {S : Scheme.{u}}
    {F G H : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (hG : Presheaf.IsSheaf (Scheme.fppfTopology.over S) G)
    (hH : Presheaf.IsSheaf (Scheme.fppfTopology.over S) H)
    (a : F ⟶ G) (b : G ⟶ H)
    (ha : relativeAlgebraicSpaces
      (@Surjective S ⊓ @Flat S ⊓ @LocallyOfFinitePresentation S :
        MorphismProperty (AlgebraicSpace S)) a),
    representableByAlgebraicSpaces (a ≫ b) ↔ representableByAlgebraicSpaces b)

end AlgebraicGeometry.AlgebraicSpace
