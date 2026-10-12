/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import stacks_project.Chap69.Definition_69_6_2_ExtensionByZero
public import stacks_project.Chap69.Definition_69_6_2_Koszul

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

/-- Definition 69.6.2: Let `S` be a scheme. Let `f : U ⟶ X` be a surjective étale
morphism of algebraic spaces over `S`. Let `F` be an object of `Ab(X_étale)`.
The alternating Čech complex associated to `F` and `f` is the cochain complex
`Hom(K^0, F) ⟶ Hom(K^1, F) ⟶ Hom(K^2, F) ⟶ ⋯` with Hom groups computed in
`Ab(X_étale)`, where `K^n = ∧^{n+1} (f_! ℤ̲)` is the truncated Koszul complex of
the trace `Tr_f : f_! ℤ̲ ⟶ ℤ̲`. -/
@[stacks 0724]
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

/-- Functoriality of the alternating Čech complex in the sheaf variable is
preadditive Yoneda applied to the truncated Koszul complex. -/
theorem alternatingCechComplexMap_app {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f]
    {F G : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}} (φ : F ⟶ G) :
    alternatingCechComplexMap f φ =
      (NatTrans.mapHomologicalComplex (preadditiveYoneda.map φ)
          (ComplexShape.up ℕ)).app (HomologicalComplex.op (koszulComplex f)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
