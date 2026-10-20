/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.Injective
import StacksCheckRecall

/-!
# Lemma 61.17.1

Inverse image along small-to-big pro-étale relocalization preserves injective
abelian sheaves and K-injective complexes. Restriction to the small pro-étale
site is the identity special case.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

variable {S T : Scheme.{u}} (f : T ⟶ S)
  [HasSheafify (topology T) AddCommGrpCat.{u + 1}]
  [HasSheafify (proetaleTopology.over S) AddCommGrpCat.{u + 1}]

/- Lemma 61.17.1 (1)(a): inverse image preserves injective abelian sheaves. -/
@[stacks 0F67] #check
  (AlgebraicGeometry.Scheme.ProEt.iInverseImage_preservesInjectiveObjects f :
    (iInverseImage f).PreservesInjectiveObjects)

section

variable [HasSheafify (topology S) AddCommGrpCat.{u + 1}]

/- Lemma 61.17.1 (1)(b): restriction to the small site preserves injectives. -/
@[stacks 0F67] #check (AlgebraicGeometry.Scheme.ProEt.iInverseImage_preservesInjectiveObjects (𝟙 S) :
    (iInverseImage (𝟙 S)).PreservesInjectiveObjects)

end

variable (I : CochainComplex
  (Sheaf (proetaleTopology.over S) AddCommGrpCat.{u + 1}) ℤ) [I.IsKInjective]

/- Lemma 61.17.1 (2)(a): inverse image preserves K-injective complexes. -/
@[stacks 0F67] #check (AlgebraicGeometry.Scheme.ProEt.iInverseImage_obj_isKInjective f I :
    CochainComplex.IsKInjective
      (((iInverseImage f).mapHomologicalComplex (up ℤ)).obj I))

section

variable [HasSheafify (topology S) AddCommGrpCat.{u + 1}]

/- Lemma 61.17.1 (2)(b): restriction to the small site preserves K-injectives. -/
@[stacks 0F67] #check (AlgebraicGeometry.Scheme.ProEt.iInverseImage_obj_isKInjective (𝟙 S) I :
    CochainComplex.IsKInjective
      (((iInverseImage (𝟙 S)).mapHomologicalComplex (up ℤ)).obj I))

end

end AlgebraicGeometry.Scheme.ProEt
