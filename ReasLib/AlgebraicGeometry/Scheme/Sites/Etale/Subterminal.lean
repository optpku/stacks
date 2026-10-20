/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A subterminal sheaf on the small étale site of a scheme is represented by a
unique open subscheme. -/
theorem existsUnique_open_of_mono_terminal
    (S : Scheme.{u})
    [HasWeakSheafify S.smallEtaleTopology (Type (u + 1))]
    (F : Sheaf S.smallEtaleTopology (Type (u + 1)))
    [Mono (terminal.from F)] :
    ∃! W : S.Opens,
      Nonempty (F ≅
        S.smallEtaleTopology.sheafifiedRepresentable (Scheme.Etale.mk W.ι)) := sorry

end AlgebraicGeometry.Scheme
