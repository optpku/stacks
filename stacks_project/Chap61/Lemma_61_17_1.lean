/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import stacks_project.Chap61.Lemma_61_17_1_InverseImage
import Mathlib.Tactic.CrossRefAttribute

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

/-- Lemma 61.17.1 (1): inverse image `iInverseImage f` from the big pro-étale site
over `S` to the small pro-étale site of `T` preserves injective abelian sheaves. -/
@[stacks 0F67]
instance iInverseImage_preservesInjectiveObjects
    {S T : Scheme.{u}} (f : T ⟶ S)
    [HasSheafify (topology T) AddCommGrpCat.{u + 1}]
    [HasSheafify (proetaleTopology.over S) AddCommGrpCat.{u + 1}] :
    (iInverseImage f).PreservesInjectiveObjects := sorry

/-- Lemma 61.17.1 (2): restriction from the big pro-étale site over `S` to the
small pro-étale site of `S`, as `iInverseImage (𝟙 S)`, preserves injective
abelian sheaves. -/
@[stacks 0F67]
instance iInverseImage_id_preservesInjectiveObjects
    (S : Scheme.{u})
    [HasSheafify (topology S) AddCommGrpCat.{u + 1}]
    [HasSheafify (proetaleTopology.over S) AddCommGrpCat.{u + 1}] :
    (iInverseImage (𝟙 S)).PreservesInjectiveObjects := sorry

/-- Lemma 61.17.1 (3): inverse image `iInverseImage f` from the big pro-étale site
over `S` to the small pro-étale site of `T` preserves K-injective cochain
complexes of abelian sheaves. -/
@[stacks 0F67]
instance iInverseImage_obj_isKInjective
    {S T : Scheme.{u}} (f : T ⟶ S)
    [HasSheafify (topology T) AddCommGrpCat.{u + 1}]
    [HasSheafify (proetaleTopology.over S) AddCommGrpCat.{u + 1}]
    (I : CochainComplex
      (Sheaf (proetaleTopology.over S) AddCommGrpCat.{u + 1}) ℤ)
    [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((iInverseImage f).mapHomologicalComplex (up ℤ)).obj I) := sorry

/-- Lemma 61.17.1 (4): restriction from the big pro-étale site over `S` to the
small pro-étale site of `S`, as `iInverseImage (𝟙 S)`, preserves K-injective
cochain complexes of abelian sheaves. -/
@[stacks 0F67]
instance iInverseImage_id_obj_isKInjective
    (S : Scheme.{u})
    [HasSheafify (topology S) AddCommGrpCat.{u + 1}]
    [HasSheafify (proetaleTopology.over S) AddCommGrpCat.{u + 1}]
    (I : CochainComplex
      (Sheaf (proetaleTopology.over S) AddCommGrpCat.{u + 1}) ℤ)
    [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((iInverseImage (𝟙 S)).mapHomologicalComplex (up ℤ)).obj I) := sorry

end AlgebraicGeometry.Scheme.ProEt
