/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Ph
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

/-!
# Definition 34.8.4

This chapter entry is a compatibility facade for standard proper-surjective
chart covers and `ph` covering families.
-/

/- Definition 34.8.4: A `ph` covering of a scheme is a family of locally
finite-type morphisms whose pullback to every affine open admits a standard
`ph` covering refining the family. -/
@[stacks 0DBG] #check (@AlgebraicGeometry.PhCovering :
  ∀ (ι : Type v) (T : AlgebraicGeometry.Scheme.{u})
    (X : ι → AlgebraicGeometry.Scheme.{u}) (π : ∀ i, X i ⟶ T), Prop)
