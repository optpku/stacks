/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.Lemma_75_8_3_InternalHom
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.MonoidalClosed
open DerivedCategory.TStructure

universe u

/- Lemma 75.8.3: if `X` is a locally Noetherian algebraic space over a scheme `S`, `K` lies in
D⁻_Coh(𝒪_X), and `L` lies in D⁺_Coh(𝒪_X), then the derived sheaf Hom RHom(K, L) lies in
D⁺_Coh(𝒪_X). -/
@[stacks 0D0S] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.InternalHom.boundedBelowCoherentCohomology :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsLocallyNoetherian X]
      [MonoidalCategory (ModuleDerived X)]
      (H : MonoidalClosed (ModuleDerived X))
      (K L : ModuleDerived X),
      DerivedCategory.cohomologyIn
          (SheafOfModules.isCoherent (structureSheaf X)) K →
        (t.minus : ObjectProperty (ModuleDerived X)) K →
          DerivedCategory.cohomologyIn
              (SheafOfModules.isCoherent (structureSheaf X)) L →
            (t.plus : ObjectProperty (ModuleDerived X)) L →
              DerivedCategory.cohomologyIn
                  (SheafOfModules.isCoherent (structureSheaf X))
                  ((ihomOf H K).obj L) ∧
                (t.plus : ObjectProperty (ModuleDerived X))
                  ((ihomOf H K).obj L))
