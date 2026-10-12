/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.CategoryTheory.Functor.Equivalence.QuasiInverse.Basic
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap75.Lemma_75_11_2_Coherator
public import stacks_project.Chap75.Lemma_75_11_3_Associated
public import stacks_project.Chap75.Lemma_75_11_3_GlobalSections
public import stacks_project.Chap75.«75_5_1_1_Comparison»

/-!
# Affine identification of the coherator on algebraic spaces

On an affine algebraic space, the coherator and derived coherator are identified
with global sections followed by the associated quasi-coherent module functor.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 75.11.3 (1). Let `S` be a scheme. Let `X` be an affine algebraic space over `S`.
Set `A = Γ(X, 𝒪_X)`. Then `Q_X : Mod(𝒪_X) ⥤ QCoh(𝒪_X)` is the functor which sends `F`
to the quasi-coherent `𝒪_X`-module associated to the `A`-module `Γ(X, F)`. -/
@[stacks 08H0]
theorem QCoh.affineCoherator_isomorphic {S : Scheme.{u}} {X : AlgebraicSpace S} [IsAffine X] :
    IsIsomorphic (QCoh.coherator X) (moduleGlobalSectionsFunctor X ⋙ QCoh.tensorOX X) :=
  sorry

/-- Lemma 75.11.3 (2). Let `S` be a scheme. Let `X` be an affine algebraic space over `S`.
Set `A = Γ(X, 𝒪_X)`. Then `RQ_X : D(𝒪_X) ⥤ D(QCoh(𝒪_X))` is the functor which sends `E`
to the complex of quasi-coherent `𝒪_X`-modules associated to the object `RΓ(X, E)` of
`D(A)`. -/
@[stacks 08H0]
theorem QCoh.Derived.affineDerivedCoherator_isomorphic {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsAffine X] :
    IsIsomorphic (QCoh.Derived.coherator X)
      (Modules.moduleDerivedGlobalSections X ⋙ (QCoh.tensorOX X).mapDerivedCategory) :=
  sorry

/-- Lemma 75.11.3 (3). Let `S` be a scheme. Let `X` be an affine algebraic space over `S`.
Restricted to `D_QCoh(𝒪_X)`, the functor `RQ_X` is a quasi-inverse to the comparison
`D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)`. -/
@[stacks 08H0]
theorem DerivedQCoh.affineCoherator_isQuasiInverse {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsAffine X] :
    (DerivedQCoh.comparison X).IsQuasiInverse
      (DerivedQCoh.inclusion X ⋙ QCoh.Derived.coherator X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
