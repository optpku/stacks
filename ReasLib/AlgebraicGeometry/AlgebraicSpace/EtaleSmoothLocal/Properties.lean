/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSmoothLocal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSmoothLocal.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSmoothLocal.Unramified
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SmoothLocal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified

/-!
# Étale-smooth locality on source-and-target for standard morphism properties

Étale, locally of finite type and locally quasi-finite, and unramified morphisms
of algebraic spaces are étale-smooth local on the source-and-target. Any property
that is smooth local on the source-and-target is a fortiori étale-smooth local.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.FiniteType

/-- The conjunction of being locally of finite type and locally quasi-finite
for morphisms of algebraic spaces is étale-smooth local on the source-and-target. -/
instance locallyQuasiFiniteIsEtaleSmoothLocalAtSourceAndTarget {S : Scheme.{u}} :
    IsEtaleSmoothLocalAtSourceAndTarget
      (@LocallyOfFiniteType S ⊓ @LocallyQuasiFinite S :
        MorphismProperty (AlgebraicSpace S)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FiniteType

namespace AlgebraicGeometry.AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget

/-- A morphism property of algebraic spaces that is smooth local on the
source-and-target is a fortiori étale-smooth local on the source-and-target. -/
instance (priority := 50) of_isSmoothLocalAtSourceAndTarget {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)} [IsSmoothLocalAtSourceAndTarget P] :
    IsEtaleSmoothLocalAtSourceAndTarget P :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget
