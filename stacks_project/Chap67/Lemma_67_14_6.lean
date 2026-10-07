module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap67.Lemma_67_14_6_Union

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

/-- Lemma 67.14.6 (1): for closed subspaces `Y = subscheme I` and `Z = subscheme J`
of an algebraic space `X` over a scheme `S`, the pushed-forward structure sheaves
fit into a short exact sequence
`0 ⟶ 𝒪_{Y ∪ Z} ⟶ 𝒪_Y × 𝒪_Z ⟶ 𝒪_{Y ∩ Z} ⟶ 0` of `𝒪_X`-modules, where the
terms are viewed as `𝒪_X`-modules via closed-immersion pushforward. -/
@[stacks 0CZ1]
theorem schemeTheoreticUnion_structureSheaf_shortExact :
    (schemeTheoreticUnionShortComplex I J).ShortExact :=
  sorry

/-- Lemma 67.14.6 (2): for closed subspaces `Y = subscheme I` and `Z = subscheme J`
of an algebraic space `X` over a scheme `S`, the square of closed-subspace
inclusions `Y ∩ Z ⟶ Y`, `Y ∩ Z ⟶ Z`, `Y ⟶ Y ∪ Z`, `Z ⟶ Y ∪ Z` is cocartesian
in `AlgebraicSpace S`, i.e. it is a pushout `Y ∪ Z ≅ Y ⨿_{Y ∩ Z} Z`. -/
@[stacks 0CZ1]
theorem schemeTheoreticUnion_isPushout :
    IsPushout (inclusion (le_sup_left : I ≤ I ⊔ J))
      (inclusion (le_sup_right : J ≤ I ⊔ J))
      (inclusion (inf_le_left : I ⊓ J ≤ I))
      (inclusion (inf_le_right : I ⊓ J ≤ J)) :=
  sorry

#check
  (inferInstance :
    IsClosedImmersion (inclusion (inf_le_left : I ⊓ J ≤ I)))

#check
  (inferInstance :
    IsClosedImmersion (inclusion (inf_le_right : I ⊓ J ≤ J)))

end AlgebraicGeometry.AlgebraicSpace
