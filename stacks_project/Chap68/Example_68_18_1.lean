module

public import ReasLib.AlgebraicGeometry.Scheme.Pullback.Fiber
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Pullback

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Pullback

/- Example 68.18.1 (1): the pair-fibre is identified with the spectrum of
the tensor product of the corresponding residue fields. -/
@[stacks 0AC3] #check (AlgebraicGeometry.Scheme.Pullback.Triplet.fiberEquiv :
    ∀ {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
      (T : AlgebraicGeometry.Scheme.Pullback.Triplet f g),
      T.fiber ≃ Spec T.tensor)

/- Example 68.18.1 (2): the pair-fibre is finite if either residue-field
extension is finite. -/
@[stacks 0AC3] #check (AlgebraicGeometry.Scheme.Pullback.Triplet.finite_fiber_of_finiteAt :
    ∀ {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
      (T : AlgebraicGeometry.Scheme.Pullback.Triplet f g),
      AlgebraicGeometry.Scheme.Hom.ResidueField.finiteAt f T.x ∨
        AlgebraicGeometry.Scheme.Hom.ResidueField.finiteAt g T.y →
      T.fiber.Finite)

/- Example 68.18.1 (3): the pair-fibre is finite when the second leg is
quasi-finite at the chosen point. -/
@[stacks 0AC3] #check (AlgebraicGeometry.Scheme.Pullback.Triplet.finite_fiber_of_quasiFiniteAt :
    ∀ {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
      (T : AlgebraicGeometry.Scheme.Pullback.Triplet f g),
      g.QuasiFiniteAt T.y → T.fiber.Finite)

end AlgebraicGeometry.Scheme.Pullback
