module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.ClosedPoint
import StacksCheckRecall

/-!
# Lemma 29.20.3

Closed points of a fibre and finite residue-field extensions.

@stack 01TF
-/

@[expose] public section

open CategoryTheory

universe u

/- Lemma 29.20.3: For a locally finite type morphism, a point is closed in its fibre exactly
when its residue field is finite over the residue field of its image. -/
@[stacks 01TF] #check
  (AlgebraicGeometry.asFiber_mem_closedPoints_iff_moduleFinite_residueField :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.LocallyOfFiniteType f] (x : X),
      f.asFiber x ∈ closedPoints (f.fiber (f x)) ↔
        Module.Finite (S.residueField (f x)) (X.residueField x))
