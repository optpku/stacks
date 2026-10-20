/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Preserves
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.FiniteEtale

/- Remark 58.5.3 (1): `FiniteEtale.toScheme X` preserves finite colimits. -/
@[stacks 0BNA]
#check (AlgebraicGeometry.Scheme.FiniteEtale.toScheme_preservesFiniteColimits :
  ∀ (X : Scheme.{u}),
    PreservesFiniteColimits (AlgebraicGeometry.Scheme.FiniteEtale.toScheme X))

/- Remark 58.5.3 (2): `FiniteEtale.toOver X` preserves finite colimits. -/
@[stacks 0BNA]
#check (AlgebraicGeometry.Scheme.FiniteEtale.toOver_preservesFiniteColimits :
  ∀ (X : Scheme.{u}),
    PreservesFiniteColimits (AlgebraicGeometry.Scheme.FiniteEtale.toOver X))

/- Remark 58.5.3 (3): `FiniteEtale.toOver X` preserves finite limits. -/
@[stacks 0BNA]
#check (AlgebraicGeometry.Scheme.FiniteEtale.toOver_preservesFiniteLimits :
  ∀ (X : Scheme.{u}),
    PreservesFiniteLimits (AlgebraicGeometry.Scheme.FiniteEtale.toOver X))

/- Remark 58.5.3 (4): `FiniteEtale.toScheme X` preserves connected finite limits. -/
@[stacks 0BNA]
#check (AlgebraicGeometry.Scheme.FiniteEtale.toScheme_preservesFiniteConnectedLimits :
  ∀ (X : Scheme.{u}),
    PreservesFiniteConnectedLimits (AlgebraicGeometry.Scheme.FiniteEtale.toScheme X))

end AlgebraicGeometry.Scheme.FiniteEtale
