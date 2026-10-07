module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroScheme.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary
public import ReasLib.Topology.Specialization.Dimension
import stacks_project.Chap42.Situation_42_7_1

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} [AlgebraicGeometry.UniversallyCatenary S]
variable (δ : S → ℤ) [IsDimensionFunction δ]
variable (X X' : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType X'.hom]
variable (f : X' ⟶ X) (ℒ : X.left.Modules) [Modules.Invertible ℒ] (s : ℒ.sections)

/- Remark 42.29.7: pulling back an invertible module and its section along an `S`-morphism
identifies the new zero scheme with the fibre product and gives a cartesian square. -/
@[stacks 0B6Y] #check (AlgebraicGeometry.Scheme.zeroSchemePullbackSquare f.left ℒ s :
    IsPullback
      (zeroSchemeι ((Modules.pullback f.left).obj ℒ) (Modules.sectionsPullback f.left ℒ s))
      (zeroSchemePullbackMap f.left ℒ s (zeroIdealSheaf_sectionsPullback f.left ℒ s))
      f.left (zeroSchemeι ℒ s))

end AlgebraicGeometry.Scheme
