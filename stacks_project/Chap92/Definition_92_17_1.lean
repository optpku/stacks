module

public import stacks_project.Chap92.«92_17_0_1_Triangle»
import StacksCheckRecall

/- Definition 92.17.1: Let A → B be a ring map. Let M be a B-module.
The map M ⟶ (L_{B/A} ⊗^L_B M)⟦1⟧ in 92.17.0.1 is called the Atiyah class of M.
This is Algebra.CotangentComplex.Atiyah.connectingMap, equivalently the third
arrow of Algebra.CotangentComplex.Atiyah.triangle. -/
@[stacks 09DE]
#check Algebra.CotangentComplex.Atiyah.connectingMap

#check Algebra.CotangentComplex.Atiyah.triangle_mor₃
#check Algebra.CotangentComplex.Atiyah.tensorModule
