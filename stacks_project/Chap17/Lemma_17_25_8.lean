/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Invertible.Small
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Site
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable (X : RingedSpace)

/- Lemma 17.25.8 (01CW): invertible `𝒪_X`-modules admit a set containing exactly one
representative of every isomorphism class. -/
@[stacks 01CW]
#check ObjectProperty.EssentiallySmall.exists_set_representatives
  (isInvertibleObject (C := X.Modules))

end AlgebraicGeometry.RingedSpace
