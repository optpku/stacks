/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Proper.Henselian
import StacksCheckRecall

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.53.9: a proper clopen subscheme of the special fibre of a separated finite-type
scheme over a henselian pair lifts to a proper clopen subscheme of the original scheme. -/
@[stacks 0CT9] #check
  (AlgebraicGeometry.Scheme.Hom.exists_clopen_proper_lift :
    ∀ {A : Type u} [CommRing A] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of A)) [IsSeparated f] [FiniteType f]
      (I : Ideal A) [HenselianRing A I]
      (Y : (pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).Opens)
      (hY : IsClopen
        (Y : Set (CategoryTheory.Limits.pullback f
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) : Scheme)))
      [IsProper
        (Y.ι ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))],
      ∃ W : X.Opens,
        IsClopen (W : Set X) ∧ IsProper (W.ι ≫ f) ∧
          (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
            pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ⟶ X) ⁻¹ᵁ W = Y)

end AlgebraicGeometry.Scheme.Hom
