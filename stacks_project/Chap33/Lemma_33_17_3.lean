/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.Proper

@[expose] public section

open CategoryTheory

universe u

/- Lemma 33.17.3 (1): every codimension-zero point belongs to the maximal open over which the
proper birational morphism is an isomorphism. -/
@[stacks 0BFP] #check
  (AlgebraicGeometry.Scheme.Hom.mem_isomorphismLocus_of_coheight_eq_zero :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X)
      [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsBirational f]
      [AlgebraicGeometry.IsProper f] [AlgebraicGeometry.IsReduced Y]
      (x : X), Order.coheight x = 0 → x ∈ f.isomorphismLocus)

/- Lemma 33.17.3 (2): every codimension-one point with discrete valuation stalk belongs to the
maximal open over which the proper birational morphism is an isomorphism. -/
@[stacks 0BFP] #check
  (AlgebraicGeometry.Scheme.Hom.mem_isomorphismLocus_of_coheight_eq_one_of_isDiscreteValuationRing :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X)
      [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsBirational f]
      [AlgebraicGeometry.IsProper f] [AlgebraicGeometry.IsReduced Y]
      (x : X), Order.coheight x = 1 →
        [IsDomain (X.presheaf.stalk x)] →
          [IsDiscreteValuationRing (X.presheaf.stalk x)] → x ∈ f.isomorphismLocus)

/- Lemma 33.17.3 (3): every normal point with finite point-set fiber belongs to the maximal
open over which the proper birational morphism is an isomorphism. -/
@[stacks 0BFP] #check
  (AlgebraicGeometry.Scheme.Hom.mem_isomorphismLocus_of_finite_preimage_singleton_of_isNormalAt :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X)
      [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsBirational f]
      [AlgebraicGeometry.IsProper f] [AlgebraicGeometry.IsReduced Y]
      (x : X), Set.Finite ((fun y : Y ↦ f y) ⁻¹' ({x} : Set X)) →
        X.isNormalAt x → x ∈ f.isomorphismLocus)

/- Lemma 33.17.3 (4): every normal point admitting a point above it where the morphism is
finite-type quasi-finite belongs to the maximal open over which the proper birational morphism
is an isomorphism. -/
@[stacks 0BFP] #check
  (AlgebraicGeometry.Scheme.Hom.mem_isomorphismLocus_of_exists_finiteTypeQuasiFiniteAt_of_isNormalAt :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X)
      [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsBirational f]
      [AlgebraicGeometry.IsProper f] [AlgebraicGeometry.IsReduced Y]
      (x : X), X.isNormalAt x →
        (∃ y : Y, f y = x ∧
          AlgebraicGeometry.Scheme.Hom.FiniteType.QuasiFiniteAt f y) →
            x ∈ f.isomorphismLocus)

end
