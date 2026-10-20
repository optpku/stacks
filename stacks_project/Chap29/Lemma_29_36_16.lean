/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Unramified
import StacksCheckRecall

open AlgebraicGeometry

universe u

variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)

/- Lemma 29.36.16
A morphism is étale at a point if and only if it is flat and G-unramified at that point.
-/
@[stacks 02GV] #check
  (AlgebraicGeometry.Scheme.Hom.etaleAt_iff_flatAt_and_gUnramifiedAt f x :
    f.EtaleAt x ↔ Scheme.Hom.flatAt f x ∧ f.GUnramifiedAt x)

#check (AlgebraicGeometry.Etale.iff_flat_and_gUnramified f :
  Etale f ↔ Flat f ∧ GUnramified f)
