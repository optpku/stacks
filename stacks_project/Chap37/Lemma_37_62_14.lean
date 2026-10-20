/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.Perfect
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IsImmersion

variable {X Y : Scheme.{u}} (i : X ⟶ Y) [IsImmersion i]
    [LocallyOfType RingHom.IsPerfectRingMap i] [IsLocallyNoetherian Y]
    [Scheme.Modules.IsFiniteLocallyFree (Scheme.Hom.conormalSheaf i)]

/- Lemma 37.62.14: A perfect immersion into a locally Noetherian scheme is regular when its
conormal sheaf is finite locally free. -/
@[stacks 0FK1] #check
  (AlgebraicGeometry.IsImmersion.isRegular_of_perfect_of_conormal i : IsRegularImmersion i)

end AlgebraicGeometry.IsImmersion
