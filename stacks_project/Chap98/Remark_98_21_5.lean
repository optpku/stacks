module

public import ReasLib.AlgebraicGeometry.Deformation.SquareZero
import StacksCheckRecall

/-!
# Short exact sequences of square-zero thickenings

A short exact sequence of deformation situations over a fixed commutative
ring `A` is recorded by exactness of the induced sequence of square-zero
kernels, which forces the first thickening to be the trivial square-zero
extension `TrivSqZeroExt A I1`.
-/

@[expose] public section

open AlgebraicGeometry.Deformation

/- Remark 98.21.5 (1): a short exact sequence of deformation situations
`(x, A1' → A) → (x, A2' → A) → (x, A3' → A)` over a fixed object `x` of a
category fibred in groupoids over `(Sch/S)_fppf` means that the induced maps
of square-zero kernels `I_i = Ker(A_i' → A)` give a short exact sequence
`0 → I3 → I2 → I1 → 0` of `A`-modules. Lean records this as
`IsShortExact f21 f32` on morphisms `f21 : Hom π2 π1` and `f32 : Hom π3 π2`
of square-zero extensions of `A`. -/
@[stacks 07YE]
#check (AlgebraicGeometry.Deformation.IsShortExact :
  {A A1' A2' A3' : Type} → [CommRing A] → [CommRing A1'] → [CommRing A2'] →
    [CommRing A3'] → {π1 : A1' →+* A} → {π2 : A2' →+* A} → {π3 : A3' →+* A} →
    [π1.IsSquareZeroExtension] → [π2.IsSquareZeroExtension] →
    [π3.IsSquareZeroExtension] →
    AlgebraicGeometry.Deformation.Hom π2 π1 →
    AlgebraicGeometry.Deformation.Hom π3 π2 → Prop)

/- Remark 98.21.5 (2): in a short exact sequence of deformation situations,
the composite `A3' → A1'` factors through `A`, so there is a canonical
isomorphism `A1' ≃+* TrivSqZeroExt A (kernelModule π1)` identifying `A1'`
with the trivial square-zero extension `A[I1]`. -/
@[stacks 07YE]
#check (AlgebraicGeometry.Deformation.trivSqZeroIso :
  {A A1' A2' A3' : Type} → [CommRing A] → [CommRing A1'] → [CommRing A2'] →
    [CommRing A3'] → {π1 : A1' →+* A} → {π2 : A2' →+* A} → {π3 : A3' →+* A} →
    [π1.IsSquareZeroExtension] → [π2.IsSquareZeroExtension] →
    [π3.IsSquareZeroExtension] →
    (f21 : AlgebraicGeometry.Deformation.Hom π2 π1) →
    (f32 : AlgebraicGeometry.Deformation.Hom π3 π2) →
    [AlgebraicGeometry.Deformation.IsShortExact f21 f32] →
    A1' ≃+* TrivSqZeroExt A
      (AlgebraicGeometry.Deformation.kernelModule π1))
