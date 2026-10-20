module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.SchemeTheoreticDensity
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StrictTransform.Comparison

/-!
# Open immersions after admissible blowups of algebraic spaces

A finite-type morphism of algebraic spaces that is an isomorphism over a
quasi-compact open of a quasi-compact, absolutely quasi-separated base becomes
an open immersion after a suitable admissible blowup, with the open remaining
scheme-theoretically dense.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.StrictTransform

/-- Let `S` be a scheme. For a finite-type morphism of algebraic spaces over
`S` that is an isomorphism over a quasi-compact open of a quasi-compact,
absolutely quasi-separated base, an admissible blowup makes the open
scheme-theoretically dense and the strict transform an open immersion. -/
theorem exists_admissibleBlowup
    {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [IsQuasiCompact B] [IsAbsolutelyQuasiSeparated B]
    (f : X ⟶ B) [FiniteType f]
    (U : OpenSubspace B) [IsQuasiCompact U.X]
    [IsIso (pullback.snd f U.ι)] :
    ∃ (B' : AlgebraicSpace S) (b : B' ⟶ B) (Z : ClosedSubspace B)
      (h_quasiCompact :
        QuasiCompact (strictTransformOpenComplement b (Z.inverseImageSubspace b) f).ι)
      (h_open : IsOpenImmersion (pullback.snd U.ι b)),
      IsBlowup b Z ∧ FinitePresentation Z.ι ∧ Disjoint Z.pointsSet U.pointsSet ∧
        IsSchemeTheoreticallyDense (pullback.snd U.ι b) ∧
          IsOpenImmersion (strictTransformSnd b (Z.inverseImageSubspace b) f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.StrictTransform
