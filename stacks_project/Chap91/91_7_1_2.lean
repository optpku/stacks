module

public import ReasLib.Topology.Sheaves.Ring.FirstOrderThickening.RelativeDiagram
import StacksCheckRecall

open CategoryTheory
open SheafOfModules.RingedSite TopologicalSpace
open TopCat.Sheaf.FirstOrderThickening

universe u

section

variable {X : TopCat.{u}}
variable [(Opens.grothendieckTopology X).HasSheafCompose
    (forget₂ CommRingCat.{u} RingCat.{u})]
variable [(Opens.grothendieckTopology X).HasSheafCompose
    (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology X) CommRingCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective CommRingCat.{u}]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {OX1 OX1' OS1 OS1' OX2 OX2' OS2 OS2' :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

/- 91.7.1.2: after identifying underlying spaces of first-order thickenings, a
commutative diagram of sheaves of rings on a space X, with front and back solutions
0 ⟶ 𝒢ⱼ ⟶ 𝒪_{X'ⱼ} ⟶ 𝒪_{Xⱼ} ⟶ 0 over 0 ⟶ 𝒥ⱼ ⟶ 𝒪_{S'ⱼ} ⟶ 𝒪_{Sⱼ} ⟶ 0,
vertical maps cⱼ, structure maps, a given g-map ν : 𝒢₁ ⟶ 𝒢₂, and with no filler
𝒪_{X'₁} ⟶ 𝒪_{X'₂}. -/
@[stacks 08UA] #check (TopCat.Sheaf.FirstOrderThickening.RelativeDiagram :
  ∀ (πX1 : OX1' ⟶ OX1) (πS1 : OS1' ⟶ OS1)
    (πX2 : OX2' ⟶ OX2) (πS2 : OS2' ⟶ OS2),
    [IsFirstOrderThickening πX1] → [IsFirstOrderThickening πS1] →
    [IsFirstOrderThickening πX2] → [IsFirstOrderThickening πS2] → Type u)
#check RelativeDiagram.of
#check RelativeDiagram.spec
#check RelativeDiagram.c
#check RelativeDiagram.Fits

end
