module

public import ReasLib.Algebra.Module.PrincipalParts.FirstOrder
public import ReasLib.Algebra.Module.PrincipalParts.Truncation
public import ReasLib.Algebra.Module.PrincipalParts.ZerothOrder

/-!
# First-order projection as truncation

The usual projection from first principal parts is the transition to zeroth principal parts,
followed by the canonical zeroth-order identification.

@stack 09CL
-/

@[expose] public section

universe u

noncomputable section

namespace PrincipalParts.FirstOrder

variable {R S M : Type u}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

/-- The first-principal-parts projection is truncation to order zero followed by the canonical
zeroth-order projection. -/
@[stacks 09CL "first-order projection"]
theorem projection_eq_truncate :
    projection (R := R) (S := S) (M := M) =
      (ZerothOrder.projection (R := R) (S := S) (M := M)).comp
        (PrincipalParts.truncate (R := R) (S := S) (M := M) (Nat.zero_le 1)) := sorry

end PrincipalParts.FirstOrder
