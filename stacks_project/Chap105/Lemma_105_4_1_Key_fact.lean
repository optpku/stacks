/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap105.Lemma_105_4_1_Key_fact_EllipticCurve
public import stacks_project.Chap105.Lemma_105_4_1_Key_fact_Functor

/-!
# Fibre products of morphisms into the moduli stack of elliptic curves
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.EllipticCurve

variable {S S' : Scheme.{u}} (E : Over S) (zero : S ⟶ E.left)
  (E' : Over S') (zero' : S' ⟶ E'.left)

/-- Lemma 105.4.1 (Key fact): The functor `Schemeᵒᵖ ⥤ Type` sending a scheme `T` to
triples `(a, a', α)`, where `a : T ⟶ S`, `a' : T ⟶ S'`, and `α` is an isomorphism of
elliptic curves over `T` from the pullback of `E` along `a` to the pullback of `E'`
along `a'`, is representable by a scheme, informally written `S ×_{M_{1,1}} S'`. -/
@[stacks 072M, instance]
theorem functor_isRepresentable [IsEllipticCurve E zero] [IsEllipticCurve E' zero'] :
    (functor E zero E' zero').IsRepresentable := sorry

end AlgebraicGeometry.EllipticCurve
