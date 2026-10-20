/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.OpenRestriction

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Compactification
namespace Of

/- Lemma 48.17.2: upper shriek commutes with restriction in a commutative square
whose horizontal morphisms are open immersions. -/
@[stacks 0G4J] #check
  (AlgebraicGeometry.Scheme.Compactification.Of.upperShriek_openRestriction_isomorphic :
    ∀ {S : Scheme.{u}} [IsNoetherian S]
      {U X V Y : FiniteTypeSeparatedOver S}
      (j : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (j' : V ⟶ Y)
      (h_comm : j ≫ f = g ≫ j')
      [IsOpenImmersion j.hom.left] [IsOpenImmersion j'.hom.left]
      (P_f : Of Y.obj.left (Over.mk f.hom.left))
      (A_f : DerivedQCoh.PlusRightAdjoint (ambientMorphism P_f))
      (P_g : Of V.obj.left (Over.mk g.hom.left))
      (A_g : DerivedQCoh.PlusRightAdjoint (ambientMorphism P_g)),
      IsIsomorphic
        (upperShriek f P_f A_f.plus ⋙
          DerivedQCoh.OpenImmersion.pullbackPlus j.hom.left)
        (DerivedQCoh.OpenImmersion.pullbackPlus j'.hom.left ⋙
          upperShriek g P_g A_g.plus))

end Of
end Compactification
end Scheme
end AlgebraicGeometry
