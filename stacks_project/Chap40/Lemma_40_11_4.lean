/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Morphism.ReducedImageClosure.Groupoid

@[expose] public section

open CategoryTheory

universe u

/-
Lemma 40.11.4: for an identity-on-objects morphism of groupoid schemes whose object scheme is
the spectrum of a perfect field, the reduced closed subscheme supported on the closure of the
arrow-map image inherits the structure of a groupoid scheme over the same base.
-/
@[stacks 04Q8] #check
  (AlgebraicGeometry.GroupoidScheme.Hom.reducedImageClosure :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
      {G₁ G₂ : AlgebraicGeometry.GroupoidScheme S},
      (eU : AlgebraicGeometry.Spec (CommRingCat.of k) ≅ G₁.U.left) →
      (hU : G₁.U = G₂.U) →
      (f : AlgebraicGeometry.GroupoidScheme.Hom G₁ G₂) →
      (hf : f.IsIdentityOnObjects hU) →
      AlgebraicGeometry.GroupoidScheme S)
