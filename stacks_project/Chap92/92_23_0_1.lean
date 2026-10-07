module

public import stacks_project.Chap92.«92_23_0_1_Solution»
import StacksCheckRecall

open RingedSite.FirstOrderThickening

universe u v

/- 92.23.0.1: given a first-order thickening t of ringed topoi with J = Ker(t♯),
a morphism f : (Sh(C), O) ⟶ (Sh(B), O_B) of ringed topoi, an O-module G, and a
map c : f⁻¹J ⟶ G of sheaves of f⁻¹O_B-modules, a solution of the diagram
0 ⟶ G ⟶ ? ⟶ O ⟶ 0 over 0 ⟶ f⁻¹J ⟶ f⁻¹O_{B'} ⟶ f⁻¹O_B ⟶ 0
is a first-order thickening i of (Sh(C), O) with Ker(i♯) identified with G
together with a morphism of thickenings (f, f') such that (f')♯ induces c. -/
@[stacks 08V4] #check RingedSite.FirstOrderThickening.Solution
#check RingedSite.FirstOrderThickening.Solution.of
#check RingedSite.FirstOrderThickening.Solution.spec
