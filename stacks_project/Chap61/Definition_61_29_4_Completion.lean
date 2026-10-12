/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.DerivedCompletion
public import stacks_project.Chap61.Definition_61_28_1_Completion

/-!
# Compatibility surface for completed constant complexes
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry.Scheme.ProEt

variable {Λ : Type w} [CommRing Λ]

/- The shared completed-constant construction is available under the established API. -/
#check (constantAdicCompletionComplex :
  ∀ {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (I : Ideal Λ),
    [HasWeakSheafify J (ModuleCat.{w} Λ)] →
      [Abelian (Sheaf J (ModuleCat.{w} Λ))] →
      CochainComplex (ModuleCat.{w} (AdicCompletion I Λ)) ℤ ⥤
        CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ)

end AlgebraicGeometry.Scheme.ProEt
