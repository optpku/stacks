/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Correspondence.Chow

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry TensorProduct

universe u

namespace AlgebraicGeometry.Correspondence

variable {k : Type u} [Field k]
variable (X Y Z : SchemeOverField k) [LocallyOfFiniteType X.hom]
  [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
variable [AlgebraicGeometry.Projective Y.hom] (r s : ℤ)

#check (Integral X Y r :
  Type (u + 1))

#check (Rational X Y r :
  Type (u + 1))

#check (RationalChowHomology X r :
  Type u)

#check (RationalChowCohomology X r :
  Type (u + 1))

#check (CompositionSpace X Y Z :
  SchemeOverField k)

#check (compositionProjection X Y Z :
  CompositionSpace X Y Z ⟶ X ⨯ Z)

#check (integralCompositionValue X Y Z :
  Integral X Y r → Integral Y Z s → Integral X Z (r + s))

#check (composition X Y Z r s :
  Rational X Y r →ₗ[ℚ] Rational Y Z s →ₗ[ℚ] Rational X Z (r + s))

end AlgebraicGeometry.Correspondence
