module

public import ReasLib.Algebra.Homology.DerivedCategory.TensorProduct.Sequential.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.Grothendieck
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Tensor.Pro
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Tensor.Triangulated
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.Pro
public import ReasLib.CategoryTheory.Pro.Sequential.Isomorphism
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived tensor products of sequential module systems

@stack 091L

Sequential inverse systems of modules inherit pointwise tensoring. This leaf
records the standard availability of its fixed-factor unbounded derived tensor
functor and the stagewise pro-isomorphism compatibility of the fixed-left
factor. The construction itself is owned by `CategoryTheory.DerivedCategory`,
while generic pro-isomorphism transport remains owned by
`CategoryTheory.Pro.SequentialHom`.
-/

@[expose] public section

open CategoryTheory
open ComplexShape

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory

section

variable {R : Type u} [CommRing R]

/-- Stacks 091L: fixed-left derived tensoring by a constant derived module preserves the
stagewise pro-isomorphism condition on derived sequential module systems. -/
@[stacks 091L]
instance SequentialModule.tensorLeftFactor
    (K : DerivedCategory (ModuleCat R)) :
    (DerivedLimit.Pro.isomorphisms (ModuleCat R)).IsPreservedBy
      (DerivedLimit.tensorLeftFactor K) := sorry

#synth MonoidalPreadditive (SequentialInverseSystem (ModuleCat R))
#synth HasDerivedCategory (SequentialInverseSystem (ModuleCat R))
#synth DerivedTensor.Has (C := SequentialInverseSystem (ModuleCat R))
#synth DerivedTensor.Right.Has (C := SequentialInverseSystem (ModuleCat R))
#synth DerivedTensor.Left.Has (C := SequentialInverseSystem (ModuleCat R))

end

end CategoryTheory.DerivedCategory
