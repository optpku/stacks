/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf
public import ReasLib.CategoryTheory.Sites.SpecialCocontinuous

/-!
# Comparison of affine and big fppf sites

The inclusion of affine schemes over a scheme into the big slice site is special cocontinuous
for the affine and big fppf topologies. Its cocontinuous direct image therefore induces an
equivalence on set-valued sheaves.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Fppf.AffineComparison

/-- The inclusion from the affine fppf site over `S` to the big fppf site over `S` is special
cocontinuous. -/
theorem isSpecialCocontinuous (S : Scheme.{u}) :
    (Scheme.AffineOver.forget S).IsSpecialCocontinuous
      (Scheme.bigAffineFppfTopology S) (Scheme.fppfTopology.over S) := sorry

/-- The affine-to-big fppf inclusion carries its canonical special-cocontinuity instance. -/
instance inclusionIsSpecialCocontinuous (S : Scheme.{u}) :
    (Scheme.AffineOver.forget S).IsSpecialCocontinuous
      (Scheme.bigAffineFppfTopology S) (Scheme.fppfTopology.over S) :=
  isSpecialCocontinuous S

/-- The inclusion from the affine fppf site over `S` to the big fppf site over `S` is
cocontinuous. -/
theorem isCocontinuous (S : Scheme.{u}) :
    (Scheme.AffineOver.forget S).IsCocontinuous
      (Scheme.bigAffineFppfTopology S) (Scheme.fppfTopology.over S) :=
  inferInstance

/-- The cocontinuous direct image from the affine fppf site to the big fppf site is an
equivalence on set-valued sheaves. -/
noncomputable instance directImageIsEquivalence (S : Scheme.{u}) :
    ((Scheme.AffineOver.forget S).sheafPushforwardCocontinuous (Type (u + 1))
      (Scheme.bigAffineFppfTopology S) (Scheme.fppfTopology.over S)).IsEquivalence :=
  CategoryTheory.Functor.IsSpecialCocontinuous.directImage_isEquivalence.{u + 1, u + 1, u, u, u + 1}
    (Scheme.AffineOver.forget S)

end AlgebraicGeometry.Scheme.Fppf.AffineComparison
