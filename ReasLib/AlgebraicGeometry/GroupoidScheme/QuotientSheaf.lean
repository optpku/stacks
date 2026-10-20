/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.Representable

/-!
# Representable quotient sheaves of groupoid schemes
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- A groupoid scheme has a representable quotient when its underlying pre-relation has a
representable quotient. -/
abbrev HasRepresentableQuotient {S : Scheme.{u}} (τ : StandardTopology)
    (G : GroupoidScheme S) : Prop :=
  Scheme.PreRelation.HasRepresentableQuotient τ G.toPreRelation

end AlgebraicGeometry.GroupoidScheme
