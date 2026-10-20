module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.VectorFields
public import stacks_project.Chap53.Lemma_53_26_1_Derivation
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Curve

/- Lemma 53.26.1 (1): every derivation of `𝒪_X` over `k` is zero when the smooth,
proper, connected curve `X` has genus at least two. -/
@[stacks 0E67]
#check (AlgebraicGeometry.Curve.derivation_eq_zero_of_two_le_genus :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Curve X] [Smooth X.hom]
    [IsProper X.hom]
    (h_genus : 2 ≤ Scheme.Hom.cohomologyFinrank X.hom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1)
    (D : derivations X.hom.toShHom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules)),
    derivationIsZero X D)

/- Lemma 53.26.1 (2): a nonzero derivation of `𝒪_X` over `k` fixes no closed point
when the smooth, proper, connected curve `X` has genus one. -/
@[stacks 0E67]
#check (AlgebraicGeometry.Curve.not_derivationFixesAt_of_genus_eq_one :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Curve X] [Smooth X.hom]
    [IsProper X.hom]
    (h_genus : Scheme.Hom.cohomologyFinrank X.hom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1 = 1)
    (D : derivations X.hom.toShHom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules))
    (hD : ¬ derivationIsZero X D) (x : closedPoints X.left),
    ¬ derivationFixesAt X D x)

/- Lemma 53.26.1 (3): a nonzero derivation of `𝒪_X` over `k` fixes at most two
closed points when the smooth, proper, connected curve `X` has genus zero. -/
@[stacks 0E67]
#check (AlgebraicGeometry.Curve.encard_derivationFixesAt_le_two_of_genus_eq_zero :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Curve X] [Smooth X.hom]
    [IsProper X.hom]
    (h_genus : Scheme.Hom.cohomologyFinrank X.hom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1 = 0)
    (D : derivations X.hom.toShHom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules))
    (hD : ¬ derivationIsZero X D),
    Set.encard {x : closedPoints X.left | derivationFixesAt X D x} ≤ 2)

end AlgebraicGeometry.Curve
