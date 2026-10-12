/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Local
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/-!
# Lemma 29.35.10

The reusable pointwise unramified-morphism API is maintained in
`ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Local`.
-/

/- Lemma 29.35.10 (1): unramifiedness at a point implies quasi-finiteness at that point. -/
@[stacks 02V5] #check
  (AlgebraicGeometry.Scheme.Hom.UnramifiedAt.quasiFiniteAt :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S} {x : X},
      f.UnramifiedAt x → f.QuasiFiniteAt x)

/- Lemma 29.35.10 (2): a globally unramified morphism is locally quasi-finite. -/
@[stacks 02V5] #check
  (AlgebraicGeometry.Unramified.locallyQuasiFinite :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S},
      AlgebraicGeometry.Unramified f → AlgebraicGeometry.LocallyQuasiFinite f)
