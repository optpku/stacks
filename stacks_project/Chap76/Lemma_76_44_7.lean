/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RegularImmersion.ConormalTransitivity
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

open Hom.Conormal.Transitivity

namespace IsH1RegularImmersion

/- Lemma 76.44.7: Let `S` be a scheme. Let `Z ⟶ Y ⟶ X` be immersions of
algebraic spaces over `S`. If `Z ⟶ Y` is `H₁`-regular, the canonical conormal
transitivity sequence is exact and étale-locally split. -/
@[stacks 09RZ] #check
  (AlgebraicGeometry.AlgebraicSpace.IsH1RegularImmersion.conormalTransitivity_isShortExactLocallySplit :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (i : Z ⟶ Y) (j : Y ⟶ X)
      [AlgebraicGeometry.AlgebraicSpace.IsH1RegularImmersion i]
      [AlgebraicGeometry.AlgebraicSpace.IsImmersion j],
      AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.Transitivity.IsShortExactLocallySplit i j)

#check
  (AlgebraicGeometry.AlgebraicSpace.IsH1RegularImmersion.conormalTransitivity_shortExact :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (i : Z ⟶ Y) (j : Y ⟶ X)
      [AlgebraicGeometry.AlgebraicSpace.IsH1RegularImmersion i]
      [AlgebraicGeometry.AlgebraicSpace.IsImmersion j],
      (AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.Transitivity.complex i j).ShortExact)

#check
  (AlgebraicGeometry.AlgebraicSpace.IsH1RegularImmersion.mono_conormalTransitivity_baseChange :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (i : Z ⟶ Y) (j : Y ⟶ X)
      [AlgebraicGeometry.AlgebraicSpace.IsH1RegularImmersion i]
      [AlgebraicGeometry.AlgebraicSpace.IsImmersion j],
      CategoryTheory.Mono (AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.Transitivity.baseChange i j))

end IsH1RegularImmersion

end AlgebraicGeometry.AlgebraicSpace
