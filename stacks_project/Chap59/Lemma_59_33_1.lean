/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.StrictHenselization

import StacksCheckRecall

open CategoryTheory Opposite
open AlgebraicGeometry

universe u v

@[expose] public section

/- Lemma 59.33.1: the stalk of the étale structure sheaf at a geometric point is identified with
the strict henselization of the local ring at its image. -/
@[stacks 04HX] #check
  (AlgebraicGeometry.Scheme.strictHenselization_iso_etaleStructureSheafStalk :
    ∀ (S : Scheme.{u}) (s : Scheme.GeometricPoint S)
      (Rsh : Type v) [CommRing Rsh]
      [Algebra (S.presheaf.stalk s.image) Rsh]
      [IsStrictHenselizationOf (S.presheaf.stalk s.image) Rsh],
      Nonempty (Rsh ≃+*
        ((@Scheme.pointSmallEtale S s.K inferInstance
          (@IsSepClosed.of_isAlgClosed s.K inferInstance s.isAlgClosed) s.hom).presheafFiber :
          (S.Etaleᵒᵖ ⥤ RingCat) ⥤ RingCat).obj
          (Scheme.Etale.Small.structureSheaf S).obj))
