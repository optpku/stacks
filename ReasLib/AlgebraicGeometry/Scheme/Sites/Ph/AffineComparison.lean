/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.Basic
public import ReasLib.CategoryTheory.Sites.SpecialCocontinuous

/-!
# Comparison of affine and big ph sites

The inclusion of affine schemes over a scheme into the big slice site is special cocontinuous
for the affine and big ph topologies. Its cocontinuous direct image therefore induces an
equivalence on set-valued sheaves.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Ph.AffineComparison

/-- The inclusion from the affine ph site over `S` to the big ph site over `S` is special
cocontinuous. -/
theorem isSpecialCocontinuous (S : Scheme.{u}) :
    (Scheme.AffineOver.forget S).IsSpecialCocontinuous
      (Scheme.bigAffinePhTopology S) (Scheme.bigPhSite S) := sorry

/-- The affine-to-big ph inclusion carries its canonical special-cocontinuity instance. -/
instance inclusionIsSpecialCocontinuous (S : Scheme.{u}) :
    (Scheme.AffineOver.forget S).IsSpecialCocontinuous
      (Scheme.bigAffinePhTopology S) (Scheme.bigPhSite S) :=
  isSpecialCocontinuous S

/-- The inclusion from the affine ph site over `S` to the big ph site over `S` is
cocontinuous. -/
theorem isCocontinuous (S : Scheme.{u}) :
    (Scheme.AffineOver.forget S).IsCocontinuous
      (Scheme.bigAffinePhTopology S) (Scheme.bigPhSite S) :=
  inferInstance

/-- The cocontinuous direct image from the affine ph site to the big ph site is an
equivalence on set-valued sheaves. -/
noncomputable instance directImageIsEquivalence (S : Scheme.{u}) :
    ((Scheme.AffineOver.forget S).sheafPushforwardCocontinuous (Type (u + 1))
      (Scheme.bigAffinePhTopology S) (Scheme.bigPhSite S)).IsEquivalence :=
  CategoryTheory.Functor.IsSpecialCocontinuous.directImage_isEquivalence.{u + 1, u + 1, u, u, u + 1}
    (Scheme.AffineOver.forget S)

end AlgebraicGeometry.Scheme.Ph.AffineComparison
