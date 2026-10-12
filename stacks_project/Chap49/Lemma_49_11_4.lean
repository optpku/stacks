/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.UniversalFiniteFree.SyntomicLocus
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace UniversalFiniteFreeAlgebra

/- Lemma 49.11.4: an open subscheme `U_d ⊆ X_d` classifying exactly the base changes of
the universal family that are syntomic is smooth over `Spec(ℤ)`. -/
@[stacks 0FL1] #check (UniversalFiniteFreeAlgebra.syntomicLocusSmooth :
  ∀ (d : ℕ+) (U_d : (baseScheme d).Opens),
    (hU_d : ∀ {X : Scheme.{0}} (f : X ⟶ baseScheme d),
      (∃ g : X ⟶ U_d.toScheme, g ≫ U_d.ι = f) ↔
        Syntomic (pullback.snd (projection d) f)) →
    Smooth (U_d.ι ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℤ (CoefficientRing d)))))

end UniversalFiniteFreeAlgebra
