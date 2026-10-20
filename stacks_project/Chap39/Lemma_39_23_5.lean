/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.InvariantBaseChange.FiniteLocallyFree
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.GroupoidScheme

section

variable {S : Scheme.{u}} (G : GroupoidScheme S)
  {A B C' : Type u} [CommRing A] [CommRing B] [CommRing C'] [Algebra A B]
  (target : A →+* B) (eU : Spec (CommRingCat.of A) ≅ G.U.left)
  (eR : Spec (CommRingCat.of B) ≅ G.R.left)
  (h_source : eR.hom ≫ G.s.left =
    Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
  (h_target : eR.hom ≫ G.t.left =
    Spec.map (CommRingCat.ofHom target) ≫ eU.hom)
  [IsFiniteLocallyFree G.s.left] [IsFiniteLocallyFree G.t.left]
  (γ : target.eqLocus (algebraMap A B) →+* C')

/- Lemma 39.23.5 (1): extending the invariant coefficient ring produces a groupoid scheme. -/
@[stacks 03BK] #check
  (AlgebraicGeometry.GroupoidScheme.invariantBaseChange
    G target eU eR h_source h_target γ : GroupoidScheme S)

/- The object scheme has the expected tensor-product affine presentation. -/
#check
  (AlgebraicGeometry.GroupoidScheme.InvariantBaseChange.objectIso
    G target eU eR h_source h_target γ :
    (invariantBaseChange G target eU eR h_source h_target γ).U.left ≅
      -- Local instance justification (defeq pin): the explicit map γ selects the coefficient Algebra structure only for this checked tensor expression.
      letI : Algebra (target.eqLocus (algebraMap A B)) C' := γ.toAlgebra
      Spec (CommRingCat.of
        (A ⊗[target.eqLocus (algebraMap A B)] C')))

/- The arrow scheme has the expected tensor-product affine presentation. -/
#check
  (AlgebraicGeometry.GroupoidScheme.InvariantBaseChange.arrowIso
    G target eU eR h_source h_target γ :
    (invariantBaseChange G target eU eR h_source h_target γ).R.left ≅
      -- Local instance justification (defeq pin): the source-induced equalizer action on B is selected only for this checked tensor expression.
      letI : Algebra (target.eqLocus (algebraMap A B)) B :=
        ((algebraMap A B).comp
          (target.eqLocus (algebraMap A B)).subtype).toAlgebra
      -- Local instance justification (defeq pin): the explicit map γ selects the coefficient Algebra structure only for this checked tensor expression.
      letI : Algebra (target.eqLocus (algebraMap A B)) C' := γ.toAlgebra
      Spec (CommRingCat.of
        (B ⊗[target.eqLocus (algebraMap A B)] C')))

/- The base-changed groupoid has a canonical projection to the original groupoid. -/
#check
  (AlgebraicGeometry.GroupoidScheme.InvariantBaseChange.projection
    G target eU eR h_source h_target γ :
    GroupoidScheme.Hom
      (invariantBaseChange G target eU eR h_source h_target γ) G)

/- The induced source map is the base change of the original source homomorphism. -/
#check
  (AlgebraicGeometry.GroupoidScheme.InvariantBaseChange.source_eq
    G target eU eR h_source h_target γ :
    -- Local instance justification (defeq pin): the source-induced equalizer action on B is selected only for this checked tensor expression.
    letI : Algebra (target.eqLocus (algebraMap A B)) B :=
      ((algebraMap A B).comp
        (target.eqLocus (algebraMap A B)).subtype).toAlgebra
    -- Local instance justification (defeq pin): the explicit map γ selects the coefficient Algebra structure only for this checked tensor expression.
    letI : Algebra (target.eqLocus (algebraMap A B)) C' := γ.toAlgebra
    (InvariantBaseChange.arrowIso G target eU eR h_source h_target γ).hom ≫
        Spec.map (CommRingCat.ofHom
          (RingHom.EqLocusBaseChange.sourceComap
            target (algebraMap A B) γ)) =
      (invariantBaseChange G target eU eR h_source h_target γ).s.left ≫
        (InvariantBaseChange.objectIso
          G target eU eR h_source h_target γ).hom)

/- The induced target map is the base change of the original target homomorphism. -/
#check
  (AlgebraicGeometry.GroupoidScheme.InvariantBaseChange.target_eq
    G target eU eR h_source h_target γ :
    -- Local instance justification (defeq pin): the source-induced equalizer action on B is selected only for this checked tensor expression.
    letI : Algebra (target.eqLocus (algebraMap A B)) B :=
      ((algebraMap A B).comp
        (target.eqLocus (algebraMap A B)).subtype).toAlgebra
    -- Local instance justification (defeq pin): the explicit map γ selects the coefficient Algebra structure only for this checked tensor expression.
    letI : Algebra (target.eqLocus (algebraMap A B)) C' := γ.toAlgebra
    (InvariantBaseChange.arrowIso G target eU eR h_source h_target γ).hom ≫
        Spec.map (CommRingCat.ofHom
          (RingHom.EqLocusBaseChange.targetComap
            target (algebraMap A B) γ)) =
      (invariantBaseChange G target eU eR h_source h_target γ).t.left ≫
        (InvariantBaseChange.objectIso
          G target eU eR h_source h_target γ).hom)

/- Lemma 39.23.5 (2)(a): every invariant after base change satisfies a positive
shifted-power equation over the new coefficient ring. -/
@[stacks 03BK] #check
  (AlgebraicGeometry.GroupoidScheme.InvariantBaseChange.shiftPower
    G target eU eR h_source h_target γ :
    -- Local instance justification (defeq pin): the source-induced equalizer action on B is selected only for this checked tensor expression.
    letI : Algebra (target.eqLocus (algebraMap A B)) B :=
      ((algebraMap A B).comp
        (target.eqLocus (algebraMap A B)).subtype).toAlgebra
    -- Local instance justification (defeq pin): the explicit map γ selects the coefficient Algebra structure only for this checked tensor expression.
    letI : Algebra (target.eqLocus (algebraMap A B)) C' := γ.toAlgebra
    ∀ f : RingHom.EqLocusBaseChange.invariantRing
        target (algebraMap A B) γ,
      f ∈ RingHom.ShiftPower.generators
        (RingHom.EqLocusBaseChange.toInvariant
          target (algebraMap A B) γ))

/- The canonical map is generated by elements satisfying shifted-power equations. -/
#check
  (AlgebraicGeometry.GroupoidScheme.InvariantBaseChange.isGenerated
    G target eU eR h_source h_target γ :
    -- Local instance justification (defeq pin): the source-induced equalizer action on B is selected only for this checked tensor expression.
    letI : Algebra (target.eqLocus (algebraMap A B)) B :=
      ((algebraMap A B).comp
        (target.eqLocus (algebraMap A B)).subtype).toAlgebra
    -- Local instance justification (defeq pin): the explicit map γ selects the coefficient Algebra structure only for this checked tensor expression.
    letI : Algebra (target.eqLocus (algebraMap A B)) C' := γ.toAlgebra
    RingHom.ShiftPower.IsGenerated
      (RingHom.EqLocusBaseChange.toInvariant
        target (algebraMap A B) γ))

/- Lemma 39.23.5 (2)(b): every element of the kernel of the canonical map has a
positive power equal to zero. -/
@[stacks 03BK] #check
  (AlgebraicGeometry.GroupoidScheme.InvariantBaseChange.kernel_nilpotent
    G target eU eR h_source h_target γ :
    -- Local instance justification (defeq pin): the source-induced equalizer action on B is selected only for this checked tensor expression.
    letI : Algebra (target.eqLocus (algebraMap A B)) B :=
      ((algebraMap A B).comp
        (target.eqLocus (algebraMap A B)).subtype).toAlgebra
    -- Local instance justification (defeq pin): the explicit map γ selects the coefficient Algebra structure only for this checked tensor expression.
    letI : Algebra (target.eqLocus (algebraMap A B)) C' := γ.toAlgebra
    ∀ f : C',
      RingHom.EqLocusBaseChange.toInvariant
          target (algebraMap A B) γ f = 0 →
        ∃ n : ℕ, 0 < n ∧ f ^ n = 0)

/- The kernel of the canonical map is locally nilpotent. -/
#check
  (AlgebraicGeometry.GroupoidScheme.InvariantBaseChange.ker_isLocallyNilpotent
    G target eU eR h_source h_target γ :
    -- Local instance justification (defeq pin): the source-induced equalizer action on B is selected only for this checked tensor expression.
    letI : Algebra (target.eqLocus (algebraMap A B)) B :=
      ((algebraMap A B).comp
        (target.eqLocus (algebraMap A B)).subtype).toAlgebra
    -- Local instance justification (defeq pin): the explicit map γ selects the coefficient Algebra structure only for this checked tensor expression.
    letI : Algebra (target.eqLocus (algebraMap A B)) C' := γ.toAlgebra
    (RingHom.ker (RingHom.EqLocusBaseChange.toInvariant
      target (algebraMap A B) γ)).IsLocallyNilpotent)

/- Lemma 39.23.5 (3): for a flat coefficient extension, the canonical map to the
base-changed invariant ring is bijective. -/
@[stacks 03BK] #check
  (AlgebraicGeometry.GroupoidScheme.InvariantBaseChange.bijective_of_flat
    G target eU eR h_source h_target γ :
    γ.Flat →
      -- Local instance justification (defeq pin): the source-induced equalizer action on B is selected only for this checked tensor expression.
      letI : Algebra (target.eqLocus (algebraMap A B)) B :=
        ((algebraMap A B).comp
          (target.eqLocus (algebraMap A B)).subtype).toAlgebra
      -- Local instance justification (defeq pin): the explicit map γ selects the coefficient Algebra structure only for this checked tensor expression.
      letI : Algebra (target.eqLocus (algebraMap A B)) C' := γ.toAlgebra
      Function.Bijective
        (RingHom.EqLocusBaseChange.toInvariant
          target (algebraMap A B) γ))

end

end AlgebraicGeometry.GroupoidScheme
