/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.UniversallyCatenary
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.DimensionFunction

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IsDualizingComplex

/- Lemma 48.2.7 (1): a locally Noetherian scheme carrying a dualizing complex is universally catenary. -/
@[stacks 0AWF] #check (AlgebraicGeometry.Scheme.IsDualizingComplex.universallyCatenary :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
      {ω : RingedSpace.ModuleDerived X.toRingedSpace},
      Scheme.IsDualizingComplex ω → UniversallyCatenary X)

/- Lemma 48.2.7 (2): the canonical normalization-degree function determined by a dualizing complex on a locally Noetherian scheme is a dimension function. -/
@[stacks 0AWF] #check (AlgebraicGeometry.Scheme.IsDualizingComplex.normalizationDegreeIsDimensionFunction :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
      {ω : RingedSpace.ModuleDerived X.toRingedSpace},
      (hω : Scheme.IsDualizingComplex ω) →
        IsDimensionFunction (AlgebraicGeometry.Scheme.IsDualizingComplex.normalizationDegree hω))

end AlgebraicGeometry.Scheme.IsDualizingComplex
