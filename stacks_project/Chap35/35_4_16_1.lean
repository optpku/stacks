/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Descent.Diagram
import StacksCheckRecall

@[expose] public section

universe u x

open CategoryTheory

variable {S S₂ S₃ : Type u}
variable [CommRing S] [CommRing S₂] [CommRing S₃]
variable (δ10 δ11 : S →+* S₂) (δ02 δ12 : S →+* S₃)
variable (δ20 δ21 δ22 : S₂ →+* S₃) (M : ModuleCat.{max u x} S)
variable (θ : ModuleCat.ExtendScalars.obj' δ10 M ≅
  ModuleCat.ExtendScalars.obj' δ11 M)
variable (h20Target : δ02 = δ20.comp δ11)
variable (h22Source : δ02 = δ22.comp δ10) (h22Target : δ12 = δ22.comp δ11)
variable (h21Target : δ12 = δ21.comp δ11)

/- 35.4.16.1: The three checks below realize the arrows
`M ⟶ M ⊗[S, δ₁¹] S₂ ⇉ M ⊗[S, δ₁₂¹] S₃` as, respectively,
`θ ∘ (1_M ⊗ δ₀¹)`, `(θ ⊗ δ₂²) ∘ (1_M ⊗ δ₀²)`, and
`1_(M ⊗ S₂) ⊗ δ₁²`. -/
@[stacks 08X0] #check
  (ModuleCat.DescentDiagram.source δ10 δ11 M θ :
    AddCommGrpCat.of M ⟶
      AddCommGrpCat.of (ModuleCat.ExtendScalars.obj' δ11 M))

#check
  (ModuleCat.DescentDiagram.upper δ10 δ11 δ02 δ12 δ20 δ22 M θ
      h20Target h22Source h22Target :
    AddCommGrpCat.of (ModuleCat.ExtendScalars.obj' δ11 M) ⟶
      AddCommGrpCat.of (ModuleCat.ExtendScalars.obj' δ12 M))

#check
  (ModuleCat.DescentDiagram.lower δ11 δ12 δ21 M h21Target :
    AddCommGrpCat.of (ModuleCat.ExtendScalars.obj' δ11 M) ⟶
      AddCommGrpCat.of (ModuleCat.ExtendScalars.obj' δ12 M))
