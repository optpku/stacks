/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Koszul

/-!
# Alternating Čech complex of a surjective étale morphism of algebraic spaces

The alternating Čech complex associated to a surjective étale morphism
`f : U ⟶ X` and an abelian sheaf `F` on `X_étale` is the cochain complex of Hom
groups `Hom(K^0, F) ⟶ Hom(K^1, F) ⟶ ⋯` in `Ab(X_étale)`, where
`K^n = ∧^{n+1} (f_! ℤ̲)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The alternating Čech complex of a surjective étale morphism `f : U ⟶ X`
and an abelian sheaf `F` is the cochain complex
`Hom(K^0, F) ⟶ Hom(K^1, F) ⟶ Hom(K^2, F) ⟶ ⋯` with Hom groups computed in
`Ab(X_étale)`, where `K^n = ∧^{n+1} (f_! ℤ̲)` is the truncated Koszul complex of
the trace `Tr_f : f_! ℤ̲ ⟶ ℤ̲`. -/
noncomputable def alternatingCechComplex {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    CochainComplex AddCommGrpCat.{u + 1} ℕ :=
  ((preadditiveYoneda.obj F).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (HomologicalComplex.op (koszulComplex f))

/-- Degree-`n` of the alternating Čech complex is `Hom(K^n, F)` in `Ab(X_étale)`. -/
theorem alternatingCechComplex_X {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) (n : ℕ) :
    (alternatingCechComplex f F).X n =
      (preadditiveYoneda.obj F).obj (Opposite.op ((koszulComplex f).X n)) :=
  sorry

/-- The differential of the alternating Čech complex is precomposition with the
Koszul differential `K^{n+1} ⟶ K^n`. -/
theorem alternatingCechComplex_d {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) (n : ℕ) :
    (alternatingCechComplex f F).d n (n + 1) =
      (preadditiveYoneda.obj F).map ((koszulComplex f).d (n + 1) n).op :=
  sorry

/-- A morphism of abelian sheaves induces a morphism of alternating Čech
complexes. -/
noncomputable def alternatingCechComplexMap {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f]
    {F G : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}} (φ : F ⟶ G) :
    alternatingCechComplex f F ⟶ alternatingCechComplex f G :=
  (NatTrans.mapHomologicalComplex (preadditiveYoneda.map φ)
      (ComplexShape.up ℕ)).app (HomologicalComplex.op (koszulComplex f))

/-- In degree `n`, the map induced by a sheaf morphism is postcomposition with
that morphism on the additive Hom group from the Koszul term. -/
theorem alternatingCechComplexMap_app {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f]
    {F G : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}} (φ : F ⟶ G) (n : ℕ) :
    (alternatingCechComplexMap f φ).f n =
      (preadditiveYoneda.map φ).app (Opposite.op ((koszulComplex f).X n)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
