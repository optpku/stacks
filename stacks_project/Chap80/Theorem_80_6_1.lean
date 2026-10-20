/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSurjective
import StacksCheckRecall

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

/- Theorem 80.6.1: an fppf sheaf with diagonal representable by algebraic spaces
and a surjective étale algebraic-space atlas is an algebraic space. -/
@[stacks 03Y3] #check
  (AlgebraicGeometry.AlgebraicSpace.IsAlgebraicSpace.of_diag_etale_surjective :
    ∀ {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
      (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
      (hΔ : representableByAlgebraicSpaces (diag F))
      {X : (Over S)ᵒᵖ ⥤ Type u} [IsAlgebraicSpace X] (a : X ⟶ F)
      (hP : (representableByAlgebraicSpaces.of_diag_isAlgebraicSpace hΔ a).has
        (@Surjective S ⊓ @Etale S : MorphismProperty (AlgebraicSpace S))),
      IsAlgebraicSpace F)

#check (AlgebraicGeometry.AlgebraicSpace.IsAlgebraicSpace.of_etale_surjective :
  ∀ {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    {X : (Over S)ᵒᵖ ⥤ Type u} [IsAlgebraicSpace X] (a : X ⟶ F)
    (ha : relativeAlgebraicSpaces
      (@Surjective S ⊓ @Etale S : MorphismProperty (AlgebraicSpace S)) a),
    IsAlgebraicSpace F)

end AlgebraicGeometry.AlgebraicSpace
