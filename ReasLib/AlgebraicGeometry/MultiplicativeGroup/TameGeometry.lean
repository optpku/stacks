/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.MultiplicativeGroup.TameDegree
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup

@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.PreGaloisCategory
noncomputable section
universe u

namespace MultiplicativeGroupTame

/-- The full tame subcategory of the smooth curve is Galois: its actual covers are
closed under finite limits, sums, subobjects and finite quotients. -/
instance cover_galois (k : Type u) [Field k] : GaloisCategory (Cover k) := by
  sorry

/-- This particular geometric fiber is a fiber functor. The existence is not eliminated
to define a replacement functor, limits, or automorphism group. -/
theorem specified_fiber_galois (k : Type u) [Field k] (η : GeometricPoint (space k)) :
    Nonempty (FiberFunctor (fiber k η)) := by
  sorry

variable (p : ℕ) [Fact p.Prime]

/-- The actual geometric kernel of the constructed tame degree morphism. -/
def geometricKernel (η : GeometricPoint (space (ZMod p))) :
    ClosedSubgroup (fundamentalGroup (ZMod p) η) where
  toSubgroup := (degreeToIntegers p η).hom.toMonoidHom.ker
  isClosed' := IsClosed.preimage (degreeToIntegers p η).hom.continuous
    (isClosed_singleton : IsClosed ({1} : Set integers))

theorem geometricKernel_mem (η : GeometricPoint (space (ZMod p)))
    (g : fundamentalGroup (ZMod p) η) :
    g ∈ geometricKernel p η ↔ degreeToIntegers p η g = 1 := Iff.rfl

/-- Full source-shaped label existence, tied to the defined closed points and ALL paths.
It is a conclusion. No chosen label or chosen path feeds the constructed data. -/
theorem exists_frobenius_labels (η : GeometricPoint (space (ZMod p))) :
    ∃ labels : ∀ d : ℕ+, points (ZMod p) d → ConjClasses (fundamentalGroup (ZMod p) η),
      ∀ (d : ℕ+) (x : points (ZMod p) d),
        labels d x ∈ frobeniusClass (ZMod p) η x.val ∧
        ∀ t : fiber (ZMod p) (pointOver (ZMod p) x.val) ≅ fiber (ZMod p) η,
          labels d x = ConjClasses.mk (frobeniusAlong (ZMod p) η x.val t) ∧
            degreeToIntegers p η (frobeniusAlong (ZMod p) η x.val t) = integerNat d.val := by
  sorry

end MultiplicativeGroupTame
