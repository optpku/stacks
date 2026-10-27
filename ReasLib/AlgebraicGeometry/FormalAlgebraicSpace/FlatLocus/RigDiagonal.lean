/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.FlatLocus
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigEtale
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigSurjective
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.FiniteType.Diagonal

/-!
# Flat loci with rig-étale and rig-surjective diagonal
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- For a locally Noetherian formal algebraic space locally of finite type over
a complete discrete valuation ring, if its relative diagonal is rig-étale and
rig-surjective, the canonical structural map from its flat locus to the formal
spectrum is an isomorphism, or the flat locus is empty: every test scheme
admitting a section of it is empty. -/
theorem flatLocus_eq_spf_or_empty {S : Scheme.{u}} {A : Type u} [CommRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
    (hA : Spec (.of A) ⟶ S) {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] (p : X ⟶ spf A hA)
    [LocallyOfFiniteType p] [RigEtale (pullback.diagonal p)]
    [RigSurjective (pullback.diagonal p)] :
    IsIso (flatLocusι p ≫ p) ∨
      ∀ T : Over S, (flatLocus p).obj (Opposite.op T) → IsEmpty T.left :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
