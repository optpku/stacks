/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.SeparatedLocallyQuasiFinite
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 80.5.2: In a cartesian square of fppf sheaves, scheme representability,
separatedness, and local quasi-finiteness descend along a surjective, flat,
locally finitely presented morphism representable by algebraic spaces. -/
@[stacks 046J] #check
  (AlgebraicGeometry.AlgebraicSpace.separatedLocallyQuasiFinite_presheaf_of_isPullback :
    ∀ {S : Scheme.{u}} {E F H G : (Over S)ᵒᵖ ⥤ Type u}
    {a : E ⟶ F} {f : E ⟶ H} {g : F ⟶ G} {b : H ⟶ G}
    (hE : Presheaf.IsSheaf (Scheme.fppfTopology.over S) E)
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (hH : Presheaf.IsSheaf (Scheme.fppfTopology.over S) H)
    (hG : Presheaf.IsSheaf (Scheme.fppfTopology.over S) G)
    (sq : IsPullback f a b g)
    (hg : relativeAlgebraicSpaces
      (@Surjective S ⊓ @Flat S ⊓ @LocallyOfFinitePresentation S :
        MorphismProperty (AlgebraicSpace S)) g)
    (ha : relativeAlgebraicSpaces
      (@Separated S ⊓ @LocallyOfFiniteType S ⊓ @LocallyQuasiFinite S :
        MorphismProperty (AlgebraicSpace S)) a),
    (over (@AlgebraicGeometry.IsSeparated ⊓ @AlgebraicGeometry.LocallyOfFiniteType ⊓
        @AlgebraicGeometry.LocallyQuasiFinite :
      MorphismProperty Scheme.{u})).presheaf b)

end AlgebraicGeometry.AlgebraicSpace
