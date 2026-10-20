/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal.OpenImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Locality
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.LocallyOfFiniteType

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocallyOfFiniteType

/-- Local finite type of scheme morphisms is étale local on the source and target. -/
instance isEtaleLocalAtSourceAndTarget :
    AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget
      (@AlgebraicGeometry.LocallyOfFiniteType :
        MorphismProperty AlgebraicGeometry.Scheme.{u}) := sorry

end AlgebraicGeometry.LocallyOfFiniteType
