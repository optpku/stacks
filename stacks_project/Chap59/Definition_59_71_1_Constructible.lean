/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u v w

namespace CategoryTheory.Sheaf

/- The shared constructibility criterion is available to source-facing chapter consumers. -/
#check (IsConstructibleEtale :
  {X : Scheme.{u}} → {D : Type w} → [Category.{v} D] →
    (∀ {Y : Scheme.{u}} (_ : Y ⟶ X),
      Sheaf X.smallEtaleTopology D → Sheaf Y.smallEtaleTopology D) →
    (∀ {Y : Scheme.{u}}, Sheaf Y.smallEtaleTopology D → Prop) →
    Sheaf X.smallEtaleTopology D → Prop)

/- The affine finite-stratification specification is available to source-facing chapter consumers. -/
#check @isConstructibleEtale_iff

end CategoryTheory.Sheaf
