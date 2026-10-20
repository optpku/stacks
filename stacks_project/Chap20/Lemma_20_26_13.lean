/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.KFlatResolution
public import ReasLib.Algebra.Homology.CochainComplex.KFlat.QuasiIso
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.Monoidal
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.RingedSpace

/- Lemma 20.26.13: tensoring an arbitrary complex with a quasi-isomorphism between K-flat
complexes preserves quasi-isomorphisms.  K-flat resolutions of `Modules X` are inferred from the
opens-ringed-site presentation. -/

variable (X : RingedSpace.{u})

@[stacks 06YG "tensoring a quasi-isomorphism between K-flat complexes"]
#check
  CochainComplex.IsKFlat.quasiIso_tensorHom_right (C := Modules X)

end AlgebraicGeometry.RingedSpace
