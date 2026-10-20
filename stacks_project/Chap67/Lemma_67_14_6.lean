module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Union

/-!
# Lemma 67.14.6

The structure-sheaf Mayer–Vietoris sequence of a scheme-theoretic union of
closed subspaces of an algebraic space, and the corresponding pushout square.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable (I J : IdealSubobject X) [IsQuasiCoherent I] [IsQuasiCoherent J]

/- Lemma 67.14.6 (1): the structure-sheaf Mayer–Vietoris sequence is short
exact after closed-immersion pushforward to the ambient algebraic space. -/
@[stacks 0CZ1] #check
  (AlgebraicGeometry.AlgebraicSpace.schemeTheoreticUnion_structureSheaf_shortExact I J :
    (schemeTheoreticUnionShortComplex I J).ShortExact)

/- Lemma 67.14.6 (2): the scheme-theoretic union is the pushout over the
scheme-theoretic intersection in algebraic spaces over the base scheme. -/
@[stacks 0CZ1] #check
  (AlgebraicGeometry.AlgebraicSpace.schemeTheoreticUnion_isPushout I J :
    IsPushout (inclusion (le_sup_left : I ≤ I ⊔ J))
      (inclusion (le_sup_right : J ≤ I ⊔ J))
      (inclusion (inf_le_left : I ⊓ J ≤ I))
      (inclusion (inf_le_right : I ⊓ J ≤ J)))

#check
  (inferInstance :
    IsClosedImmersion (inclusion (inf_le_left : I ⊓ J ≤ I)))

#check
  (inferInstance :
    IsClosedImmersion (inclusion (inf_le_right : I ⊓ J ≤ J)))

end AlgebraicGeometry.AlgebraicSpace
