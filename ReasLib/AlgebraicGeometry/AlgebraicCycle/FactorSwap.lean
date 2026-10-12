/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Product
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Proper
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.Affine
public import ReasLib.RingTheory.Catenary.Field

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicCycle

/-- Exchange the factors of a product cycle by proper pushforward along the product braiding. -/
noncomputable def swapEquiv {k : Type u} [Field k] (X Y : SchemeOverField k) :
    AlgebraicCycle (X ⨯ Y).left ℤ ≃+ AlgebraicCycle (Y ⨯ X).left ℤ where
  toFun := fun z ↦ map (Limits.prod.braiding X Y).hom.left
    (fun _ ↦ (0 : ℤ)) (fun _ ↦ (0 : ℤ)) z
  invFun := fun z ↦ map (Limits.prod.braiding X Y).inv.left
    (fun _ ↦ (0 : ℤ)) (fun _ ↦ (0 : ℤ)) z
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry

/-- Factor exchange sends a cycle to pushforward along the product braiding. -/
theorem swapEquiv_apply {k : Type u} [Field k] (X Y : SchemeOverField k)
    (z : AlgebraicCycle (X ⨯ Y).left ℤ) :
    swapEquiv X Y z = map (Limits.prod.braiding X Y).hom.left
      (fun _ ↦ (0 : ℤ)) (fun _ ↦ (0 : ℤ)) z := sorry

/-- Applying factor exchange twice recovers the original algebraic cycle. -/
theorem swapEquiv_swap {k : Type u} [Field k] (X Y : SchemeOverField k)
    (z : AlgebraicCycle (X ⨯ Y).left ℤ) :
    swapEquiv Y X (swapEquiv X Y z) = z := sorry

end AlgebraicGeometry.AlgebraicCycle
