/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.SchemeTheoreticDensity
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Lemma_67_17_2_InverseImage
public import stacks_project.Chap67.Lemma_67_17_8_SchemeTheoreticImage

/-!
# Étale-local tests for scheme-theoretic density

An open immersion of algebraic spaces satisfies the étale-local
scheme-theoretic density tests when the scheme-theoretic closure of every
étale preimage equals the source, equivalently when some surjective étale
scheme atlas has this property.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.SchemeTheoreticDensity

#check (AlgebraicGeometry.AlgebraicSpace.SchemeTheoreticDensity.forallEtale :
  ∀ {S : Scheme.{u}} {X U : AlgebraicSpace S} (ι : U ⟶ X) [IsOpenImmersion ι],
    Prop)

#check (AlgebraicGeometry.AlgebraicSpace.SchemeTheoreticDensity.forallEtale_iff :
  ∀ {S : Scheme.{u}} {X U : AlgebraicSpace S} (ι : U ⟶ X) [IsOpenImmersion ι],
    forallEtale ι ↔
    ∀ (V : AlgebraicSpace S) (φ : V ⟶ X),
      Etale φ → IsSchemeTheoreticallyDominant (openInverseImageι φ ι))

#check (AlgebraicGeometry.AlgebraicSpace.SchemeTheoreticDensity.forallEtale.of :
  ∀ {S : Scheme.{u}} {X U : AlgebraicSpace S} (ι : U ⟶ X) [IsOpenImmersion ι]
    (h : ∀ {V : AlgebraicSpace S} (φ : V ⟶ X),
    Etale φ → IsSchemeTheoreticallyDominant (openInverseImageι φ ι)),
    forallEtale ι)

#check (AlgebraicGeometry.AlgebraicSpace.SchemeTheoreticDensity.forallEtale.spec :
  ∀ {S : Scheme.{u}} {X U : AlgebraicSpace S} (ι : U ⟶ X) [IsOpenImmersion ι]
    (h : forallEtale ι) {V : AlgebraicSpace S} (φ : V ⟶ X)
    (hφ : Etale φ),
    IsSchemeTheoreticallyDominant (openInverseImageι φ ι))

#check (AlgebraicGeometry.AlgebraicSpace.SchemeTheoreticDensity.existsSurjectiveEtale :
  ∀ {S : Scheme.{u}} {X U : AlgebraicSpace S} (ι : U ⟶ X) [IsOpenImmersion ι],
    Prop)

#check (AlgebraicGeometry.AlgebraicSpace.SchemeTheoreticDensity.existsSurjectiveEtale_iff :
  ∀ {S : Scheme.{u}} {X U : AlgebraicSpace S} (ι : U ⟶ X) [IsOpenImmersion ι],
    existsSurjectiveEtale ι ↔
    ∃ (V : Over S) (φ : ofOver V ⟶ X),
      Etale φ ∧ Surjective φ ∧
        IsSchemeTheoreticallyDominant (openInverseImageι φ ι))

#check (AlgebraicGeometry.AlgebraicSpace.SchemeTheoreticDensity.existsSurjectiveEtale.of :
  ∀ {S : Scheme.{u}} {X U : AlgebraicSpace S} (ι : U ⟶ X) [IsOpenImmersion ι]
    {V : Over S} (φ : ofOver V ⟶ X) [Etale φ] [Surjective φ]
    (h : IsSchemeTheoreticallyDominant (openInverseImageι φ ι)),
    existsSurjectiveEtale ι)

#check (AlgebraicGeometry.AlgebraicSpace.SchemeTheoreticDensity.existsSurjectiveEtale.spec :
  ∀ {S : Scheme.{u}} {X U : AlgebraicSpace S} (ι : U ⟶ X) [IsOpenImmersion ι]
    (h : existsSurjectiveEtale ι),
    ∃ (V : Over S) (φ : ofOver V ⟶ X),
      Etale φ ∧ Surjective φ ∧
        IsSchemeTheoreticallyDominant (openInverseImageι φ ι))

end AlgebraicGeometry.AlgebraicSpace.SchemeTheoreticDensity
