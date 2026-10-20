/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.ChosenPresentation.SmallToBig

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.ChosenBigProetaleSite

variable (X : ChosenBigProetaleSite.{u, v}) (S : X.carrier)

/- Definition 61.12.14: in the situation of Lemma 61.12.13, the functor
`i_S⁻¹ = π_{S,*}` is the restriction to the small pro-étale site. For a sheaf
`ℱ` on the chosen big pro-étale site, `ℱ|_{S_proétale}` denotes the value of
this functor on `ℱ`. -/
@[stacks 098R] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.SmallToBig.inverseImage (𝟙 S) :
    Sheaf (bigTopology X S) (Type (max u v)) ⥤
      Sheaf (smallTopology X S) (Type (max u v)))

end AlgebraicGeometry.ChosenBigProetaleSite
