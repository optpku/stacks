module

import stacks_project.Chap97.«97_13_0_2_FreeDimAlgebra»
import stacks_project.Chap97.«97_13_0_2_Functor»
import StacksCheckRecall

universe u

/- 97.13.0.2: `FA d` is the functor `Sch_fppfᵒᵖ ⥤ Groupoids` sending a scheme `T`
to the groupoid of free `d`-dimensional algebras over `Γ(T, ⊤)`. The fppf
decoration is the ambient site `Scheme.fppfTopology`, not a restriction of
objects. -/
@[stacks 05YN] #check
  (@AlgebraicGeometry.FA : ∀ (d : ℕ) [NeZero d],
    CategoryTheory.Functor (AlgebraicGeometry.Scheme.{u})ᵒᵖ
      CategoryTheory.Grpd.{u, u})
