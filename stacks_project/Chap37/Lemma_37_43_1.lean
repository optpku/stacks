/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Normalization
import StacksCheckRecall

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FiniteType f] [IsSeparated f]

/- Lemma 37.43.1: a finite-type separated morphism is an isomorphism over an open
part of its relative normalization whose inverse image is exactly its quasi-finite locus. -/
@[stacks 03GW] #check
  (AlgebraicGeometry.Scheme.Hom.FiniteType.exists_isIso_morphismRestrict_toNormalization f :
    ∃ U' : f.normalization.Opens,
      IsIso (f.toNormalization ∣_ U') ∧
        ((f.toNormalization ⁻¹ᵁ U' : X.Opens) : Set X) =
          {x : X | f.QuasiFiniteAt x})

end AlgebraicGeometry
