/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.«92_11_1_1_Comparison»
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat

/-!
# The comparison map `(J ⟶ Ω_{P/A} ⊗_P B) ⟶ L_{B/A}` in `D(A)`
-/

@[expose] public section

open CategoryTheory
open CommRingCat.Under.FreeAlgebra

noncomputable section

universe u

namespace CategoryTheory.CommRingCat.Under
namespace CotangentComplex

/-- The inclusion of `L_{B/A}` into the standard-resolution mapping cone of `𝒥 ⟶ Ω` is a
quasi-isomorphism, since `Lπ_!(𝒥) = 0`. -/
instance omegaInr_quasiIso (A : CommRingCat.{u}) (B : Under A) :
    QuasiIso (omegaInr A B) := sorry

/-- Quasi-isomorphisms become isomorphisms in the derived category. -/
instance omegaInr_isIso (A : CommRingCat.{u}) (B : Under A) :
    IsIso (DerivedCategory.Q.map (omegaInr A B)) := inferInstance

/-- 92.11.1.1: let `A ⟶ B` be a ring map. For any object `U = (P ⟶ B)` of `C_{B/A}`,
writing `J = Ker(P ⟶ B)`, there is a canonical morphism
`(J ⟶ Ω_{P/A} ⊗_P B) ⟶ L_{B/A}` in `D(A)`, obtained by evaluating the sheaf complex
`𝒥 ⟶ Ω` at `U` and using `Lπ_!(𝒥 ⟶ Ω) = L_{B/A}`. -/
@[stacks 08R8]
def comparisonDerived (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    DerivedCategory.Q.obj (kernelDifferentialsComplex A B E φ) ⟶
      DerivedCategory.Q.obj (objRestrictScalars A B) :=
  DerivedCategory.Q.map (evaluationToMappingCone A B E φ) ≫
    (asIso (DerivedCategory.Q.map (omegaInr A B))).inv

/-- The labeled comparison is the 08Q6 evaluation of `𝒥 ⟶ Ω` at `φ`, transported along the
quasi-isomorphism `Lπ_!(𝒥 ⟶ Ω) ≅ L_{B/A}` computed on the standard polynomial resolution. -/
theorem comparisonDerived_fac (A : CommRingCat.{u}) (B : Under A) (E : Type u)
    (φ : (functor A).obj E ⟶ B) :
    comparisonDerived A B E φ =
      DerivedCategory.Q.map (evaluationToMappingCone A B E φ) ≫
        (asIso (DerivedCategory.Q.map (omegaInr A B))).inv := sorry

end CotangentComplex
end CategoryTheory.CommRingCat.Under
