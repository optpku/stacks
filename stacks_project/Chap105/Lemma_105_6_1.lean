module

public import stacks_project.Chap105.Definition_105_4_3_Smooth
public import stacks_project.Chap105.Definition_105_5_1_Algebraic
public import stacks_project.Chap105.Lemma_105_6_1_Moduli
public import stacks_project.Chap105.Lemma_105_6_1_Weierstrass

/-!
# Lemma 105.6.1

The classifying 1-morphism `W ⟶ M₁₁` of the universal Weierstrass family is smooth and
surjective as a 1-morphism of categories fibred in groupoids over `Sch / Spec ℤ`.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.M11

/-- Lemma 105.6.1 (1): the classifying 1-morphism `W ⟶ M₁₁` given by the universal
Weierstrass family `(E_W, f_W, 0_W)` is a smooth 1-morphism of categories fibred in
groupoids over `Sch / Spec ℤ`. -/
@[stacks 072T]
instance weierstrassCover_smooth :
    Groupoids.Hom.SmoothOnSchemes weierstrassCover.{u} := sorry

/-- Lemma 105.6.1 (2): the classifying 1-morphism `W ⟶ M₁₁` given by the universal
Weierstrass family `(E_W, f_W, 0_W)` is a surjective 1-morphism of categories fibred in
groupoids over `Sch / Spec ℤ`. -/
@[stacks 072T]
theorem weierstrassCover_surjective :
    EllipticCurve.Moduli.surjectiveOnSchemes weierstrassCover.{u} := sorry

end AlgebraicGeometry.M11
