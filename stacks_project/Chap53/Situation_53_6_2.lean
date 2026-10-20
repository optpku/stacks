/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Topology.KrullDimension
import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
import ReasLib.AlgebraicGeometry.Scheme.OverField

universe u

open AlgebraicGeometry

section

variable {k : Type u} [Field k]
variable (X : SchemeOverField k) [IsProper X.hom]
variable (h_dimension : topologicalKrullDim X.left = 1)
variable (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))

/- Situation 53.6.2: `k` is a field and `X` is a proper scheme over `k` of
topological Krull dimension `1`, with bijective canonical map `k → Γ(X, 𝒪_X)`. -/
@[stacks 0B5D] #check (AlgebraicGeometry.Scheme.Hom.globalSectionsMap X.hom :
  k →+* AlgebraicGeometry.Scheme.globalSectionsRing X.left)

/- Field assumption: `k` is a field. -/
#check (inferInstance : Field k)

/- Properness assumption: `X` is a proper scheme over `k`. -/
#check (inferInstance : IsProper X.hom)

/- Dimension assumption: `X` has topological Krull dimension `1`. -/
#check (h_dimension : topologicalKrullDim X.left = 1)

/- Bijectivity assumption: the canonical map `k → Γ(X, 𝒪_X)` is bijective. -/
#check
  (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))

end
