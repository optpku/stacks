/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import ReasLib.CategoryTheory.Limits.Shapes.Pullback.Graph

/-!
# Graph morphisms over a base scheme

The graph itself is the generic categorical `pullback.graph`.  This file owns
the geometric properties and reusable instances special to schemes.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry
namespace Scheme.Hom

universe u

variable {X Y S : Scheme.{u}} (x : X ⟶ S) (y : Y ⟶ S) (g : X ⟶ Y)
  (hg : g ≫ y = x)

/-- The raw pullback graph of a scheme morphism over a common base is an immersion. -/
@[stacks 01KS "raw graph immersion", instance]
instance graph_isImmersion :
    IsImmersion (pullback.graph x y g hg) := sorry

/-- The raw pullback graph into a separated scheme over a common base is a closed immersion. -/
@[stacks 01KS "raw closed graph", instance]
instance graph_isClosedImmersion [IsSeparated y] :
    IsClosedImmersion (pullback.graph x y g hg) := sorry

/-- The raw pullback graph into a quasi-separated scheme over a common base is quasi-compact. -/
@[stacks 01KS "raw quasi-compact graph", instance]
instance graph_quasiCompact [QuasiSeparated y] :
    QuasiCompact (pullback.graph x y g hg) := sorry

end Scheme.Hom
end AlgebraicGeometry
