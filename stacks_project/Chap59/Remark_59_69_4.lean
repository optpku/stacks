/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

/-!
# Remark 59.69.4 (03RS): an alternative excision proof

Source: `etale-cohomology.tex`, `remark-natural-proof`, immediately following
`lemma-vanishing-cohomology-mu-smooth-curve` (Lemma 59.69.3, tag 03RR).

Here `X` is an affine smooth curve over an algebraically closed field `k`,
`n` is invertible in `k`, and `Xbar` is a smooth projective compactification
of `X`. The preceding result computes the small étale cohomology of `μₙ`:
degree zero is `μₙ(k)`, degree one is noncanonically a free `ZMod n`-module
of rank `2g + r - 1`, and degrees at least two vanish. Here `g` is the genus
of `Xbar` and `r` is the number of boundary points.

The remark says that the natural alternative proof is to excise `X` from
`Xbar`, and explicitly states that this cohomological theory has not been
developed in the source. This is a comment about a proof method, not a new
assertion identifying excision with formation of a set complement.

This source entry records that remark as commentary. It does not claim to
construct an étale localization sequence or supply an alternative proof.
-/
