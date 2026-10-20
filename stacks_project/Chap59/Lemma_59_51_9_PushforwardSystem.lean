/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SheafImage
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SheafSystem.Pushforward

/-! Compatibility checks for the shared small-etale sheaf image API. -/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Etale

/- The shared direct-image operation remains available to chapter consumers. -/
#check (pushforwardAlong : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
  Sheaf X.smallEtaleTopology (Type (u + 1)) →
    Sheaf Y.smallEtaleTopology (Type (u + 1)))

end AlgebraicGeometry.Scheme.Etale
