module

public import stacks_project.Chap72.Definition_72_7_4_Class
public import stacks_project.Chap99.Situation_99_11_1_PicardGroup

/-!
# Picard comparison with the Weil divisor class group

On a locally Noetherian integral algebraic space, the Weil divisor class of an
invertible module induces a canonical additive homomorphism from the Picard group
to the Weil divisor class group.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} (X : AlgebraicSpace S)
variable [IsLocallyNoetherian X] [IsIntegral X]

/-- The canonical comparison homomorphism from the Picard group of a locally
Noetherian integral algebraic space to its Weil divisor class group, sending the
class of an invertible module to its Weil divisor class. -/
noncomputable def picardToWeilDivisorClassGroup :
    X.PicardGroup →+ WeilDivisorClassGroup X :=
  AddMonoidHom.mk' (fun x ↦ invertibleModuleWeilDivisorClass (PicardGroup.repr x))
    sorry

/-- The comparison homomorphism evaluates on a Picard class as the Weil divisor
class of the chosen representative. -/
theorem picardToWeilDivisorClassGroup_repr (x : X.PicardGroup) :
    picardToWeilDivisorClassGroup X x =
      invertibleModuleWeilDivisorClass (PicardGroup.repr x) :=
  sorry

/-- The comparison homomorphism assigns to an invertible module its Weil divisor
class. -/
theorem picardToWeilDivisorClassGroup_picardClass
    (L : X.Modules) [isInvertibleObject L] :
    picardToWeilDivisorClassGroup X (Modules.picardClass L) =
      invertibleModuleWeilDivisorClass L :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
