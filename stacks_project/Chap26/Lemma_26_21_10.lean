/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Graph
import StacksCheckRecall

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory Limits

universe u

variable {S : Scheme.{u}} {X Y : CategoryTheory.Over S} (g : X ⟶ Y)

/- Lemma 26.21.10 (1): a graph over a common base is an immersion. -/
@[stacks 01KS] #check (inferInstance : IsImmersion (CategoryTheory.Over.graph g))
#check CategoryTheory.Over.graph_isPullback g

section

variable [IsSeparated Y.hom]

/- Lemma 26.21.10 (2): a graph into a separated target is a closed immersion. -/
@[stacks 01KS] #check
  (inferInstance : IsClosedImmersion (CategoryTheory.Over.graph g))

end

section

variable [QuasiSeparated Y.hom]

/- Lemma 26.21.10 (3): a graph into a quasi-separated target is quasi-compact. -/
@[stacks 01KS] #check (inferInstance : QuasiCompact (CategoryTheory.Over.graph g))

end
end AlgebraicGeometry
