/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap91.«91_13_1_2_Diagram»
import StacksCheckRecall

/- 91.13.1.2: after identifying underlying topoi of first-order thickenings and reducing
to sheaves on one site C (with f₁ = f₂ = id on topoi), the displayed diagram of sheaves
of rings, with front and back solutions 0 ⟶ 𝒢ⱼ ⟶ 𝒪'ⱼ ⟶ 𝒪ⱼ ⟶ 0 over
0 ⟶ fⱼ⁻¹ 𝒥ⱼ ⟶ fⱼ⁻¹ 𝒪_{B'ⱼ} ⟶ fⱼ⁻¹ 𝒪_{Bⱼ} ⟶ 0, where 𝒢ⱼ = Ker(iⱼ^♯),
vertical maps cⱼ : fⱼ⁻¹ 𝒥ⱼ ⟶ 𝒢ⱼ, NNW arrows the g⁻¹-maps of the front row including
a given g⁻¹𝒪₁-module map ν : g⁻¹𝒢₁ ⟶ 𝒢₂, and with no filler 𝒪'₁ ⟶ 𝒪'₂. -/
@[stacks 08UI] #check @SheafOfModules.RingedSite.FirstOrderThickening.RelativeDiagram
