/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Remark_67_20_9_Factorization
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Remark 67.20.9: for a quasi-compact and quasi-separated morphism `f : X ⟶ Y` of
algebraic spaces over a scheme `S`, `f` factors canonically as
`X ⟶ relativeSpec (pushforwardStructureQcAlgebra f) ⟶ Y`. -/
@[stacks 081X] #check
  (Hom.toPushforwardRelativeSpec :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f],
      X ⟶ relativeSpec (pushforwardStructureQcAlgebra f))

@[stacks 081X] #check
  (fun {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f] ↦
    relativeSpecπ (pushforwardStructureQcAlgebra f))

@[stacks 081X] #check
  (Hom.toPushforwardRelativeSpec_comp_relativeSpecπ :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f],
      Hom.toPushforwardRelativeSpec f ≫
          relativeSpecπ (pushforwardStructureQcAlgebra f) =
        f)
