/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Closed.ModuleCat.Iterated
import StacksCheckRecall

/-!
# Tensor to an iterated Hom complex

The complex-level map is owned by `CategoryTheory.CochainComplex.InternalHom.Module.iterated`.
Its functoriality is inherited from the generic closed-monoidal construction, while summand and
projection calculations use the fine-grained `Module.Iterated` coordinate API.

@stack 0A60
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CochainComplex.HomComplex

variable {R : Type u} [CommRing R]
variable (K L M : CochainComplex (ModuleCat R) ℤ)

/- Lemma 15.72.6: the canonical map
`Hom^•(L, M) ⊗ K ⟶ Hom^•(Hom^•(K, L), M)`. -/
@[stacks 0A60 "tensor-to-iterated module-valued Hom comparison"]
#check CategoryTheory.CochainComplex.InternalHom.Module.iterated K L M

#check @CategoryTheory.CochainComplex.InternalHom.Module.iterated_natural_source
#check @CategoryTheory.CochainComplex.InternalHom.Module.iterated_natural_middle
#check @CategoryTheory.CochainComplex.InternalHom.Module.iterated_natural_target
#check @CategoryTheory.CochainComplex.InternalHom.Module.Iterated.coordinate
#check @CategoryTheory.CochainComplex.InternalHom.Module.Iterated.component_tmul_apply
#check @CategoryTheory.CochainComplex.InternalHom.Module.Iterated.componentBlock
#check @CategoryTheory.CochainComplex.InternalHom.Module.Iterated.componentBlock_π
#check @CategoryTheory.CochainComplex.InternalHom.Module.Iterated.block
#check @CategoryTheory.CochainComplex.InternalHom.Module.Iterated.block_isIso

#print axioms CategoryTheory.CochainComplex.InternalHom.Module.iterated
#print axioms CategoryTheory.CochainComplex.InternalHom.Module.Iterated.component
