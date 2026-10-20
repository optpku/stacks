/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.V.Stability
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u v w

/-!
# Lemma 34.10.9

This chapter entry is a compatibility facade for the stability API of `V`
covering families.
-/

/- Lemma 34.10.9 (1): an isomorphism is a singleton `V` covering. -/
@[stacks 0ETJ] #check
  (AlgebraicGeometry.isVCovering_singleton_of_isIso :
    ∀ {T T' : AlgebraicGeometry.Scheme.{u}} (f : T' ⟶ T) [CategoryTheory.IsIso f],
      AlgebraicGeometry.IsVCovering T (fun _ : Unit ↦ T') (fun _ ↦ f))

/- Lemma 34.10.9 (2): composing a `V` covering family with a `V` covering
family over each member gives a `V` covering. -/
@[stacks 0ETJ] #check
  (AlgebraicGeometry.IsVCovering.comp :
    ∀ {T : AlgebraicGeometry.Scheme.{u}} {ι : Type v} {κ : ι → Type w}
        (family : ι → AlgebraicGeometry.Scheme.{u}) (map : ∀ i, family i ⟶ T)
        (refining : ∀ i, κ i → AlgebraicGeometry.Scheme.{u})
        (refiningMap : ∀ i j, refining i j ⟶ family i)
        (hfamily : AlgebraicGeometry.IsVCovering T family map)
        (hrefining : ∀ i, AlgebraicGeometry.IsVCovering
          (family i) (refining i) (refiningMap i)),
      AlgebraicGeometry.IsVCovering T (fun p : Sigma κ ↦ refining p.1 p.2)
        (fun p ↦ refiningMap p.1 p.2 ≫ map p.1))

/- Lemma 34.10.9 (3): pullback along an arbitrary scheme morphism preserves
a `V` covering family. -/
@[stacks 0ETJ] #check
  (AlgebraicGeometry.IsVCovering.pullback :
    ∀ {T T' : AlgebraicGeometry.Scheme.{u}} {ι : Type v}
        (family : ι → AlgebraicGeometry.Scheme.{u}) (map : ∀ i, family i ⟶ T)
        (hfamily : AlgebraicGeometry.IsVCovering T family map) (g : T' ⟶ T),
      AlgebraicGeometry.IsVCovering T' (fun i : ι ↦ pullback (map i) g)
        (fun i ↦ pullback.snd (map i) g))
