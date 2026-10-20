/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResolutionProperty.AffineDiagonal
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 76.56.6: a quasi-compact and quasi-separated algebraic space `X` over a
scheme `S` with the resolution property has affine diagonal over `ℤ` as in
Definition 66.3.1, i.e. `diag (extendBaseTerminal X)` is representable affine. -/
@[stacks 0GV3] #check (AlgebraicGeometry.AlgebraicSpace.affineDiagonal_of_hasResolutionProperty :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsQuasiCompact X]
    [IsAbsolutelyQuasiSeparated X], SheafOfModules.HasResolutionProperty (structureSheaf X) →
    (MorphismProperty.over (@IsAffineHom)).presheaf (diag (extendBaseTerminal X)))

end AlgebraicGeometry.AlgebraicSpace
