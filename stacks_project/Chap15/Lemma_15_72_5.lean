/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Closed.ModuleCat.Source
import StacksCheckRecall

/-!
# Tensor/internal-Hom unit

The canonical closed braided unit is transported once to the module-valued Hom complex by
`CategoryTheory.CochainComplex.InternalHom.Module.tensorUnit`.

@stack 0A62
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open CategoryTheory.MonoidalClosed
open CategoryTheory.CochainComplex.InternalHom

variable {R : Type u} [CommRing R]
variable (K L : CochainComplex (ModuleCat R) ℤ)

/- Lemma 15.72.5: the canonical map `K ⟶ (L ⟶[Cpx] (K ⊗ L))`. -/
@[stacks 0A62 "tensor/internal-Hom unit for module cochain complexes"]
#check Module.tensorUnit (R := R) K L

#check @Module.tensorUnit_natural_left
#check @Module.tensorUnit_natural_right
#check @tensorInternalHomUnit
#check @tensorInternalHomUnit_spec
#check @tensorInternalHomUnit_natural_left
#check @tensorInternalHomUnit_natural_right
