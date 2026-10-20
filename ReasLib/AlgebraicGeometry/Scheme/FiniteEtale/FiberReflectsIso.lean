module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-!
# Reflection of isomorphisms by a finite étale geometric fiber

For a connected base, bijectivity on one geometric fiber forces the finite
étale morphism to have rank one on each connected component of its target.
The inverse is supplied by the native finite-flat rank-one construction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable {X : Scheme.{u}}
variable {K : Type u} [Field K] [IsAlgClosed K]
variable (point : Spec (.of K) ⟶ X)

/-- A bijection on the specified geometric fiber makes the rank of the
finite étale map equal to one everywhere on its target. Every connected
component of the target meets this fiber, and rank is locally constant.
This is the rank argument of Stacks, Tag 0BNB. -/
theorem finrank_eq_one_of_finiteFiber_bijective [ConnectedSpace X] {Y Z : FiniteEtale X} (f : Y ⟶ Z)
    (hf : Function.Bijective ((finiteFiber point).map f)) :
    Scheme.Hom.finrank f.left = 1 := sorry

/-- The reverse cover map uses the actual inverse scheme morphism obtained
from finite-flat rank one; it remains over the same base. -/
def inverseOfFiniteFiberBijective [ConnectedSpace X] {Y Z : FiniteEtale X} (f : Y ⟶ Z)
    (hf : Function.Bijective ((finiteFiber point).map f)) : Z ⟶ Y := by
  letI : IsFinite Z.hom := Z.prop.1
  letI hsep : IsSeparated Z.hom := IsSeparated.of_isAffineHom Z.hom
  letI hfinite : IsFinite (f.left ≫ Z.hom) := by
    rw [MorphismProperty.Over.w f]
    exact Y.prop.1
  letI : IsFinite f.left := @IsFinite.of_comp Y.left Z.left X f.left Z.hom hfinite hsep
  letI : Etale Z.hom := Z.prop.2
  letI : Etale (f.left ≫ Z.hom) := by
    rw [MorphismProperty.Over.w f]
    exact Y.prop.2
  letI : Etale f.left := MorphismProperty.of_postcomp (W := @Etale) (W' := @Etale)
    f.left Z.hom Z.prop.2 inferInstance
  letI : IsIso f.left := (Scheme.Hom.isIso_iff_finrank_eq f.left).mpr
    (finrank_eq_one_of_finiteFiber_bijective point f hf)
  exact MorphismProperty.Over.homMk (inv f.left) (by sorry)

/-- The reverse map is a left inverse of the specified cover morphism. -/
theorem inverseOfFiniteFiberBijective_comp [ConnectedSpace X]
    {Y Z : FiniteEtale X} (f : Y ⟶ Z)
    (hf : Function.Bijective ((finiteFiber point).map f)) :
    inverseOfFiniteFiberBijective point f hf ≫ f = 𝟙 Z := sorry

/-- The reverse map is a right inverse of the specified cover morphism. -/
theorem comp_inverseOfFiniteFiberBijective [ConnectedSpace X]
    {Y Z : FiniteEtale X} (f : Y ⟶ Z)
    (hf : Function.Bijective ((finiteFiber point).map f)) :
    f ≫ inverseOfFiniteFiberBijective point f hf = 𝟙 Y := sorry

/-- Reflection of an isomorphism uses the specified inverse cover map. -/
instance finiteFiber_reflectsIsomorphisms [ConnectedSpace X] :
    (finiteFiber point).ReflectsIsomorphisms where
  reflects f h := by
    let hf := ConcreteCategory.bijective_of_isIso ((finiteFiber point).map f)
    exact ⟨⟨inverseOfFiniteFiberBijective point f hf,
      comp_inverseOfFiniteFiberBijective point f hf,
      inverseOfFiniteFiberBijective_comp point f hf⟩⟩

end AlgebraicGeometry.Scheme.FiniteEtale
