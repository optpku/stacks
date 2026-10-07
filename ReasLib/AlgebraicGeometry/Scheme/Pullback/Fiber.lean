module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.ResidueField
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField.Extension

/-!
# Pair-fibres of scheme pullbacks

The pair-fibre of a `Triplet` is the set of points of `X ×_S Y` lying over a
fixed compatible pair, together with its identification with the spectrum of
the tensor product of residue fields.
-/

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Pullback

variable {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}

namespace Triplet

/-- The pair-fibre of a pullback triplet `T`, consisting of those points of
`X ×_S Y` that project to `T.x` and `T.y`. -/
def fiber (T : Triplet f g) : Set (pullback f g : Scheme) :=
  {w | pullback.fst f g w = T.x ∧ pullback.snd f g w = T.y}

/-- A point of the scheme pullback lies in the pair-fibre of `T` if and only if
its two projections are `T.x` and `T.y`. -/
theorem mem_fiber_iff (T : Triplet f g) (w : (pullback f g : Scheme)) :
    w ∈ T.fiber ↔ pullback.fst f g w = T.x ∧ pullback.snd f g w = T.y :=
  sorry

/-- The canonical map from `Spec T.tensor` lands in the pair-fibre of `T`. -/
theorem specTensorTo_mem_fiber (T : Triplet f g) (p : Spec T.tensor) :
    T.SpecTensorTo p ∈ T.fiber :=
  sorry

/-- The concrete map from the pair-fibre of `T` to `Spec T.tensor`. -/
noncomputable def fiberToSpec (T : Triplet f g) : T.fiber → Spec T.tensor :=
  fun w =>
    Spec.map (tensorCongr (Triplet.ext w.2.1 w.2.2)).inv (SpecOfPoint w.1)

/-- The concrete map from `Spec T.tensor` to the pair-fibre of `T`. -/
noncomputable def specToFiber (T : Triplet f g) : Spec T.tensor → T.fiber :=
  fun p =>
    ⟨T.SpecTensorTo p, ⟨T.fst_SpecTensorTo_apply p, T.snd_SpecTensorTo_apply p⟩⟩

/-- The map `specToFiber` is a left inverse of `fiberToSpec`. -/
theorem specToFiber_leftInverse (T : Triplet f g) :
    Function.LeftInverse T.specToFiber T.fiberToSpec :=
  sorry

/-- The map `specToFiber` is a right inverse of `fiberToSpec`. -/
theorem specToFiber_rightInverse (T : Triplet f g) :
    Function.RightInverse T.specToFiber T.fiberToSpec :=
  sorry

/-- The canonical identification of the pair-fibre of `T` with `Spec T.tensor`. -/
noncomputable def fiberEquiv (T : Triplet f g) : T.fiber ≃ Spec T.tensor where
  toFun := T.fiberToSpec
  invFun := T.specToFiber
  left_inv := T.specToFiber_leftInverse
  right_inv := T.specToFiber_rightInverse

/-- The inverse of `fiberEquiv` is the underlying point of `SpecTensorTo`. -/
theorem fiberEquiv_symm_apply (T : Triplet f g) (p : Spec T.tensor) :
    (T.fiberEquiv.symm p).1 = T.SpecTensorTo p :=
  sorry

/-- The image of `SpecTensorTo` is exactly the pair-fibre of `T`. -/
theorem range_specTensorTo (T : Triplet f g) :
    Set.range T.SpecTensorTo = T.fiber :=
  sorry

/-- The pair-fibre is finite if the residue-field extension along the first
leg is finite. -/
theorem finite_fiber_of_finiteAt_fst (T : Triplet f g)
    (hfin : ResidueField.finiteAt f T.x) : T.fiber.Finite :=
  sorry

/-- The pair-fibre is finite if the residue-field extension along the second
leg is finite. -/
theorem finite_fiber_of_finiteAt_snd (T : Triplet f g)
    (hfin : ResidueField.finiteAt g T.y) : T.fiber.Finite :=
  sorry

/-- The pair-fibre is finite if either residue-field extension is finite. -/
theorem finite_fiber_of_finiteAt (T : Triplet f g)
    (hfin : ResidueField.finiteAt f T.x ∨ ResidueField.finiteAt g T.y) :
    T.fiber.Finite :=
  sorry

/-- The pair-fibre is finite if the second leg is quasi-finite at `T.y`. -/
theorem finite_fiber_of_quasiFiniteAt (T : Triplet f g)
    (hg : g.QuasiFiniteAt T.y) : T.fiber.Finite :=
  sorry

end Triplet

end AlgebraicGeometry.Scheme.Pullback
