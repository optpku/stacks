/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Remark 49.2.11: a locally finite-type and locally quasi-finite morphism between locally
Noetherian schemes has a relative dualizing sheaf, unique up to a unique isomorphism compatible
with all affine relative-dualizing identifications. -/
@[stacks 0BVG] #check
  (AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf.existsUnique :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
      [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
      [LocallyOfFiniteType f] [LocallyQuasiFinite f],
      ∃ W : AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf f,
        ∀ W' : AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf f,
          ∃! i : W.module.obj ≅ W'.module.obj,
            AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf.Compatible f W W' i)
