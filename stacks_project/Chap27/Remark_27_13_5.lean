/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.MorphismProperties
import StacksCheckRecall

@[expose] public section

universe u

/- Remark 27.13.5: finite type is missing from the preceding list of properties because the notion
has not yet been defined at this point. Smoothness is another omitted property, and there are
many more such properties. In particular, the canonical projection from projective space over a
scheme to that scheme is of finite type and smooth. -/
@[stacks 01NI] #check
  (AlgebraicGeometry.ProjectiveSpace.toBase_finiteType :
    ∀ (n : ℕ) (S : AlgebraicGeometry.Scheme.{u}),
      AlgebraicGeometry.Scheme.Hom.FiniteType
        (AlgebraicGeometry.ProjectiveSpace.toBase n S))

#check
  (AlgebraicGeometry.ProjectiveSpace.toBase_smooth :
    ∀ (n : ℕ) (S : AlgebraicGeometry.Scheme.{u}),
      AlgebraicGeometry.Smooth (AlgebraicGeometry.ProjectiveSpace.toBase n S))
