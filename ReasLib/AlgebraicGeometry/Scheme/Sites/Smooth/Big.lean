/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Smooth.Affine
public import ReasLib.CategoryTheory.Sites.Over.Topos

/-!
# Big smooth sheaf functors

This leaf specializes the topology-independent slice-site topos morphism to
the big smooth topology on schemes.
-/

@[expose] public section

open CategoryTheory
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Smooth
namespace Big

variable {S T : Scheme.{u}}

/-- The morphism of topoi on big smooth slice sites induced by a scheme morphism. -/
noncomputable abbrev morphismOfTopoi (f : T ⟶ S) :
    MorphismOfTopoiIn (Scheme.smoothOverTopology S)
      (Scheme.smoothOverTopology T) :=
  CategoryTheory.Over.Site.morphismOfTopoi.{u + 1, u, u + 1}
    (Scheme.grothendieckTopology @Smooth) f

end Big
end Smooth
end Scheme
end AlgebraicGeometry
