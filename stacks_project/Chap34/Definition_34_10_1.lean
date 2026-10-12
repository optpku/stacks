/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Cover.V.Basic

@[expose] public section

/-!
# Definition 34.10.1

This chapter entry is a compatibility facade for valuative extensions, finite
affine families, and standard `V` covers.
-/

universe u

#check IsExtensionOfValuationRings
#check AlgebraicGeometry.AffineFamilyOver

/- Definition 34.10.1: a standard `V` covering is a finite affine family over an affine scheme
with the valuative lifting property after extending the valuation ring. -/
@[stacks 0ETB] #check
  (AlgebraicGeometry.AffineFamilyOver.IsStandardVCover :
    ∀ {T : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.AffineFamilyOver T → Prop)
