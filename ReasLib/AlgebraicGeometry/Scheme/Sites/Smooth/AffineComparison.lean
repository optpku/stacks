/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Smooth.StandardAffine
public import ReasLib.CategoryTheory.Sites.SpecialCocontinuous
import ReasLib.AlgebraicGeometry.Scheme.Cover.Smooth.StandardRefinement

/-!
# Comparison of affine and big smooth sites

The inclusion of affine schemes over a scheme into the big slice site is special cocontinuous
for the standard affine and big smooth topologies. Its cocontinuous direct image therefore
induces an equivalence on set-valued sheaves.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Smooth.AffineComparison

/-- The inclusion from the standard affine smooth site over `S` to the big smooth site over
`S` is special cocontinuous. -/
theorem isSpecialCocontinuous (S : Scheme.{u}) :
    (Scheme.AffineOver.forget S).IsSpecialCocontinuous
      (Scheme.Smooth.StandardAffine.topology S)
      (Scheme.smoothOverTopology S) := sorry

/-- The affine-to-big smooth inclusion carries its canonical special-cocontinuity instance. -/
instance inclusionIsSpecialCocontinuous (S : Scheme.{u}) :
    (Scheme.AffineOver.forget S).IsSpecialCocontinuous
      (Scheme.Smooth.StandardAffine.topology S)
      (Scheme.smoothOverTopology S) :=
  isSpecialCocontinuous S

/-- The cocontinuous direct image from the standard affine smooth site to the big smooth site
is an equivalence on set-valued sheaves. -/
noncomputable instance directImageIsEquivalence (S : Scheme.{u}) :
    ((Scheme.AffineOver.forget S).sheafPushforwardCocontinuous (Type (u + 1))
      (Scheme.Smooth.StandardAffine.topology S)
      (Scheme.smoothOverTopology S)).IsEquivalence :=
  CategoryTheory.Functor.IsSpecialCocontinuous.directImage_isEquivalence.{u + 1, u + 1, u, u, u + 1}
    (Scheme.AffineOver.forget S)

end AlgebraicGeometry.Scheme.Smooth.AffineComparison
