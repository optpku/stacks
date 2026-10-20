/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeHom.Postcomposition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeHom.SheafHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiniteLocallyFree

/-!
# Étale postcomposition on relative morphisms

For a finite locally free source, postcomposition along an étale morphism is
representable by algebraic spaces and étale. Surjectivity is preserved as well.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

/-- For a finite locally free source, every scheme-test pullback of postcomposition along
an étale morphism is represented by an algebraic space étale over the test scheme. -/
theorem postcomp_etale {S : Scheme.{u}} {B : AlgebraicSpace S}
    {Z X' X : Over B} (f : X' ⟶ X) [Etale f.left] [FiniteLocallyFree Z.hom]
    (U : Over S) (ξ : Pair Z.hom X.hom U) :
    ∃ (F : AlgebraicSpace S) (p : F ⟶ ofOver U)
      (q : toSheaf.obj F ⟶ sheaf Z.hom X'.hom),
      Etale p ∧
        IsPullback q (toSheaf.map p) (postcompose f)
          (SpacePair.toSheafHom ((SpacePair.schemeEquiv Z X U).symm ξ)) :=
  sorry

/-- For a finite locally free source, every scheme-test pullback of postcomposition along
an étale surjective morphism is represented by an algebraic space étale and surjective
over the test scheme. -/
theorem postcomp_surjective {S : Scheme.{u}} {B : AlgebraicSpace S}
    {Z X' X : Over B} (f : X' ⟶ X) [Etale f.left] [FiniteLocallyFree Z.hom]
    [Surjective f.left] (U : Over S) (ξ : Pair Z.hom X.hom U) :
    ∃ (F : AlgebraicSpace S) (p : F ⟶ ofOver U)
      (q : toSheaf.obj F ⟶ sheaf Z.hom X'.hom),
      Etale p ∧ Surjective p ∧
        IsPullback q (toSheaf.map p) (postcompose f)
          (SpacePair.toSheafHom ((SpacePair.schemeEquiv Z X U).symm ξ)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
