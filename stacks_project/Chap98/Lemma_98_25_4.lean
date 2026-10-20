/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Noetherian.Representability
import StacksCheckRecall

/-!
# Lemma 98.25.4

A limit-preserving sheaf transformation on `(Sch/S)_τ` is representable if and
only if its restriction to `(Noetherian/S)_τ` is representable, and if and only
if this can be tested on affine finite type objects mapping into an affine open
of `S`.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Over
open AlgebraicGeometry.StandardTopology

universe u

/- Lemma 98.25.4: representability of a transformation between limit-preserving
sheaves is equivalent to representability of its restriction to locally
Noetherian schemes, and can be tested on affine finite type objects mapping
into an affine open of the base. -/
@[stacks 0GE5] #check
  (AlgebraicGeometry.StandardTopology.relativelyRepresentable_restrict_iff :
    ∀ (τ : StandardTopology) {S : Scheme.{u}} [IsLocallyNoetherian S]
      {F' G' : (Over S)ᵒᵖ ⥤ Type (u + 1)}
      (hF' : isLimitPreservingSheaf τ S F') (hG' : isLimitPreservingSheaf τ S G')
      (a' : F' ⟶ G'),
      uliftYoneda.{u + 1}.relativelyRepresentable a' ↔
        uliftYoneda.{u + 1}.relativelyRepresentable ((restrictPresheaf S).map a'))

#check
  (AlgebraicGeometry.StandardTopology.relativelyRepresentable_restrict_iff_affineFiniteType :
    ∀ (τ : StandardTopology) {S : Scheme.{u}} [IsLocallyNoetherian S]
      {F' G' : (Over S)ᵒᵖ ⥤ Type (u + 1)}
      (hF' : isLimitPreservingSheaf τ S F') (hG' : isLimitPreservingSheaf τ S G')
      (a' : F' ⟶ G'),
      uliftYoneda.{u + 1}.relativelyRepresentable ((restrictPresheaf S).map a') ↔
        relativelyRepresentableOnAffineFiniteType ((restrictPresheaf S).map a'))
