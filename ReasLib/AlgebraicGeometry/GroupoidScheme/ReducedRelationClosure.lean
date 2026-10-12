/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Morphism.ReducedImageClosure

/-!
# Reduced relation closures of groupoid schemes

This module defines the outer-pair map on composable pairs in the reduced closure of the
canonical relation of a groupoid scheme and records its set-theoretic stability over a field.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The outer-pair morphism on composable pairs in the reduced closure of the image of
the canonical `(t, s)` morphism of a groupoid scheme. -/
noncomputable def reducedRelationClosureComposition {S : Scheme.{u}} (G : GroupoidScheme S) :
    let i := Scheme.Hom.reducedImageClosureιOver G.toPreRelation.hom
    Limits.pullback (i ≫ prod.snd) (i ≫ prod.fst) ⟶ G.U ⨯ G.U :=
  let i := Scheme.Hom.reducedImageClosureιOver G.toPreRelation.hom
  prod.lift
    (Limits.pullback.fst (i ≫ prod.snd) (i ≫ prod.fst) ≫ i ≫ prod.fst)
    (Limits.pullback.snd (i ≫ prod.snd) (i ≫ prod.fst) ≫ i ≫ prod.snd)

/-- If the object scheme is isomorphic to the spectrum of a field, the outer-pair morphism
on composable pairs in the reduced relation closure lands set-theoretically in that closure. -/
theorem reducedRelationClosureComposition_range_subset
    {S : Scheme.{u}} {k : Type u} [Field k] (G : GroupoidScheme S)
    (eU : Spec (CommRingCat.of k) ≅ G.U.left) :
    Set.range (reducedRelationClosureComposition G).left ⊆
      Set.range (Scheme.Hom.reducedImageClosureιOver G.toPreRelation.hom).left := sorry

end AlgebraicGeometry.GroupoidScheme
