module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Proetale.Family

@[expose] public section

/-!
# Definition 61.12.1

This chapter entry is a compatibility facade for canonical pro-étale covering
families and their finite affine-refinement characterization.
-/

universe u v

/- Definition 61.12.1: A pro-étale covering of a scheme `T` is an indexed family
of morphisms to `T` whose members are weakly étale and which admits a finite affine
refinement over every affine open of `T`. -/
@[stacks 0989] #check (AlgebraicGeometry.Scheme.Proetale.IsCovering :
  {T : AlgebraicGeometry.Scheme.{u}} → {ι : Type v} →
    (ι → CategoryTheory.Over T) → Prop)

#check (AlgebraicGeometry.Scheme.Proetale.isCovering_iff_finiteAffineRefinement :
  {T : AlgebraicGeometry.Scheme.{u}} → {ι : Type v} →
    (family : ι → CategoryTheory.Over T) →
      AlgebraicGeometry.Scheme.Proetale.IsCovering family ↔
        (∀ i : ι, AlgebraicGeometry.WeaklyEtale (family i).hom) ∧
          ∀ U : T.Opens, AlgebraicGeometry.IsAffineOpen U →
            ∃ n : ℕ,
              ∃ a : Fin n → ι,
                ∃ V : (j : Fin n) → ((family (a j)).left).Opens,
                  (∀ j : Fin n, AlgebraicGeometry.IsAffineOpen (V j)) ∧
                    (⋃ j : Fin n,
                      (family (a j)).hom.base ''
                        (V j : Set (family (a j)).left.carrier)) =
                      (U : Set T.carrier))
