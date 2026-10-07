module

import StacksCheckRecall
public import ReasLib.RingTheory.Smooth.AtPrime.FieldExtension

@[expose] public section

/-!
# Smoothness at a Prime under Field Extension Recall

@stack 02UQ

The shared leaf separates the principal-open source-facing formulation from
mathlib's canonical local predicate, so consumers need no local finite-type to
finite-presentation instance construction.
-/

/- Lemma 10.137.18, tag 02UQ: for a finite-type `k`-algebra `S`, a field
extension `K / k`, and `qK : Spec(K ⊗[k] S)`, smoothness at the contraction of
`qK` is equivalent to smoothness at `qK`. -/
@[stacks 02UQ "smoothness at a prime under field extension"]
#check @Algebra.SmoothAtPrime.iff_tensorProduct_fieldExtension

@[stacks 02UQ "canonical IsSmoothAt field-extension criterion"]
#check @Algebra.IsSmoothAt.iff_tensorProduct_fieldExtension
