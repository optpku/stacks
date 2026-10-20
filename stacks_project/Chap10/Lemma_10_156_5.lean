/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Algebra.TensorProduct.Locality
import StacksCheckRecall

@[expose] public section

/-!
# Locality of an integral tensor product

@stack 092Y

Lemma 10.156.5 is recalled through the neutral tensor-product locality API.
The reusable statement records the local-map and integrality proofs explicitly
and tests pure inseparability on the canonical maps of residue fields, so no
chapter-specific residue-field algebra instance or chosen auxiliary point is
needed downstream.
-/

/- Lemma 10.156.5, tag `092Y`: for local maps `A → B` and `A → C` of local
commutative rings, if `A → C` is integral and either canonical residue-field
map `ResidueField A →+* ResidueField C` or `ResidueField A →+* ResidueField B`
is purely inseparable, then `B ⊗[A] C` is local and both tensor inclusions are
local homomorphisms. -/
@[stacks 092Y]
#check @Algebra.TensorProduct.Locality.residueFieldPurelyInseparable
#check @Algebra.TensorProduct.Locality.isLocalRing
#check @Algebra.TensorProduct.Locality.includeLeft_isLocalHom
#check @Algebra.TensorProduct.Locality.includeRight_isLocalHom
