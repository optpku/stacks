/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.GlobalSections.Invertible
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Pullback

/-!
# Picard groups under faithfully flat affine base change

Pullback along a faithfully flat affine base change is injective on the Picard
group of a quasi-compact, quasi-separated scheme with semilocal global sections.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AffineBaseChange

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

/-- Pullback on Picard groups along a faithfully flat affine base change is injective when the
source scheme is quasi-compact and quasi-separated and has semilocal global sections. -/
@[stacks 0CDY]
theorem picardPullback_injective
    [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]
    [Finite (MaximalSpectrum (Γ(X, ⊤)))]
    (hff : (algebraMap A B).FaithfullyFlat) :
    Function.Injective (Scheme.Hom.picardPullback (AffineBaseChange.toSource A B f)) := sorry

end AlgebraicGeometry.Scheme.AffineBaseChange
