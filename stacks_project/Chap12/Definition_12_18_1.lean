module

public import Mathlib.Algebra.Homology.HomologicalBicomplex
import StacksCheckRecall

@[expose] public section

open CategoryTheory ComplexShape

universe v u

variable {V : Type u} [Category.{v} V] [Limits.HasZeroMorphisms V]

/- Definition 12.18.1 [012Y]: a cohomological double complex is the canonical bicomplex type
`HomologicalComplex₂ V (up ℤ) (up ℤ)`. -/
@[stacks 012Y]
#check (HomologicalComplex₂ V (up ℤ) (up ℤ))

/- The horizontal square-zero, vertical square-zero, and commuting-square laws are exposed by the
owner APIs rather than repeated as chapter-local fields. -/
#check @HomologicalComplex₂.d_f_comp_d_f
#check @HomologicalComplex.d_comp_d
#check @HomologicalComplex₂.d_comm
