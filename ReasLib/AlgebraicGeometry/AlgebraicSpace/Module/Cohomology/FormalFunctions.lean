/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Topology.Homeomorph.Defs
public import ReasLib.Algebra.Category.ModuleCat.Topology.Limit
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.IdealPower.Quotient

/-!
# Formal functions for coherent cohomology of algebraic spaces

The maps `H^p(X, F) / I^n H^p(X, F) ⟶ H^p(X, F / I^n F)` assemble to a morphism
from the I-adic completion of `H^p(X, F)` to the inverse limit of the quotient
cohomology system. For a coherent sheaf on an algebraic space proper over a
Noetherian affine base, this map is an isomorphism and a homeomorphism for the
limit topologies.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology
open CategoryTheory CategoryTheory.ConcreteCategory CategoryTheory.Limits Opposite

noncomputable section

universe u

variable {A : Type u} [CommRing A]
variable {X : AlgebraicSpace (Spec (CommRingCat.of A))}

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `cohomologyOver`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology

/-- The ideal power `I^n` annihilates the image of `H^p(X, F)` in
`H^p(X, F / I^n F)`, so it is contained in the kernel of
`toQuotientCohomology`. -/
theorem pow_smul_le_ker_toQuotientCohomology (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p n : ℕ) :
    I ^ n • (⊤ : Submodule A
        (GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p)) ≤
      LinearMap.ker (toQuotientCohomology I f F p n).hom :=
  sorry

/-- The descended comparison `H^p(X, F) / I^n H^p(X, F) ⟶ H^p(X, F / I^n F)`. -/
def toQuotientModPow (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p n : ℕ) :
    ModuleCat.of A
      (GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p ⧸
        I ^ n • (⊤ : Submodule A
          (GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p))) ⟶
      quotientCohomology I f F p n :=
  ConcreteCategory.ofHom
    ((I ^ n • (⊤ : Submodule A
        (GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p))).liftQ
      (toQuotientCohomology I f F p n).hom
      (pow_smul_le_ker_toQuotientCohomology I f F p n))

/-- Composing `toQuotientModPow` with the quotient map recovers
`toQuotientCohomology`. -/
theorem toQuotientModPow_comp_mkQ (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p n : ℕ) :
    (toQuotientModPow I f F p n).hom ∘ₗ
        Submodule.mkQ
          (I ^ n • (⊤ : Submodule A
            (GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p))) =
      (toQuotientCohomology I f F p n).hom :=
  Submodule.liftQ_mkQ _ _ _

/-- The descended comparisons are natural with respect to the adic quotient
transitions and the cohomology tower. -/
theorem toQuotientModPow_natural (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p : ℕ) {m n : ℕ} (h : m ≤ n) :
    ModuleCat.ofHom
        (AdicCompletion.transitionMap I
          (GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p) h) ≫
        toQuotientModPow I f F p m =
      toQuotientModPow I f F p n ≫ (quotientSystem I f F p).transitionMap h :=
  by
    apply ModuleCat.hom_ext
    apply Submodule.linearMap_qext
    ext x
    change (toQuotientCohomology I f F p m).hom x =
      ((quotientSystem I f F p).transitionMap h).hom
        ((toQuotientCohomology I f F p n).hom x)
    exact (congrArg (fun k ↦ k.hom x)
      (toQuotientCohomology_natural I f F p h)).symm

/-- Evaluations on the adic completion followed by the descended comparisons
form a natural family of morphisms to the quotient cohomology system. -/
theorem limitComparison_naturality (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p : ℕ)
    (sourceIndex targetIndex : ℕᵒᵖ) (g : sourceIndex ⟶ targetIndex) :
    𝟙 (ModuleCat.of A
        (AdicCompletion I
          (GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p))) ≫
        ConcreteCategory.ofHom
          (((toQuotientModPow I f F p targetIndex.unop).hom ∘ₗ
              AdicCompletion.eval I
                (GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p)
                targetIndex.unop) :
            AdicCompletion I
                (GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p) →ₗ[A]
              quotientCohomology I f F p targetIndex.unop) =
      ConcreteCategory.ofHom
          (((toQuotientModPow I f F p sourceIndex.unop).hom ∘ₗ
              AdicCompletion.eval I
                (GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p)
                sourceIndex.unop) :
            AdicCompletion I
                (GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p) →ₗ[A]
              quotientCohomology I f F p sourceIndex.unop) ≫
        (quotientSystem I f F p).map g :=
  sorry

/-- The induced map from the I-adic completion of `H^p(X, F)` to the inverse
limit of `H^p(X, F / I^n F)`. -/
def limitComparison (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p : ℕ) :
    ModuleCat.of A
      (AdicCompletion I
        (GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p)) ⟶
      limit (quotientSystem I f F p) :=
  limit.lift (quotientSystem I f F p)
    { pt := ModuleCat.of A
        (AdicCompletion I
          (GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p))
      π :=
        { app := fun n ↦
            ConcreteCategory.ofHom
              ((toQuotientModPow I f F p n.unop).hom ∘ₗ
                AdicCompletion.eval I
                  (GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p)
                  n.unop)
          naturality := fun {sourceIndex targetIndex} g ↦
            limitComparison_naturality I f F p sourceIndex targetIndex g } }

/-- Projecting `limitComparison` to stage `n` is evaluation on the completion
followed by `toQuotientModPow`. -/
theorem limitComparison_comp_π (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p n : ℕ) :
    limitComparison I f F p ≫ limit.π (quotientSystem I f F p) (op n) =
      ModuleCat.ofHom
        ((toQuotientModPow I f F p n).hom ∘ₗ
          AdicCompletion.eval I
            (GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p) n) :=
  limit.lift_π _ _

/-- For a coherent sheaf on an algebraic space proper over a Noetherian affine
base, the canonical comparison from completed cohomology to the inverse limit
of ideal-power quotient cohomology is an isomorphism of modules in every degree. -/
@[stacks 08AZ]
instance isIso_limitComparison [IsNoetherianRing A] (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) [Proper f]
    (F : X.Modules) [F.IsCoherent]
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p : ℕ) :
    IsIso (limitComparison I f F p) :=
  sorry

/-- For a coherent sheaf on an algebraic space proper over a Noetherian affine
base, the canonical comparison from completed cohomology to the inverse limit
of ideal-power quotient cohomology is a homeomorphism for the limit topologies. -/
@[stacks 08AZ]
theorem isHomeomorph_limitComparison [IsNoetherianRing A] (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) [Proper f]
    (F : X.Modules) [F.IsCoherent]
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p : ℕ) :
    @IsHomeomorph
      (AdicCompletion I
        (GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p))
      (limit (quotientSystem I f F p) : ModuleCat A)
      (⨅ n, TopologicalSpace.induced
        (AdicCompletion.eval I
          (GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p) n) ⊥)
      (Functor.limitTopology (quotientSystem I f F p))
      (limitComparison I f F p).hom :=
  sorry

set_option backward.isDefEq.respectTransparency false in
/-- The canonical quotient-cohomology maps form a natural family along the
ideal-power quotient cohomology system. -/
theorem toLimit_naturality (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p : ℕ)
    (sourceIndex targetIndex : ℕᵒᵖ) (g : sourceIndex ⟶ targetIndex) :
    𝟙 (GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p) ≫
        toQuotientCohomology I f F p targetIndex.unop =
      toQuotientCohomology I f F p sourceIndex.unop ≫
        (quotientSystem I f F p).map g :=
  by
    have hg : (homOfLE (leOfHom g.unop)).op = g := Subsingleton.elim _ _
    have hn := (toQuotientCohomology_natural I f F p (leOfHom g.unop)).symm
    dsimp only [SequentialInverseSystem.transitionMap] at hn
    rw [hg] at hn
    simpa only [Category.id_comp, quotientSystem] using hn

/-- The canonical comparison `H^p(X, F) ⟶ lim_n H^p(X, F / I^n F)` induced by
`toQuotientCohomology`. -/
def toLimit (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p : ℕ) :
    GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p ⟶
      limit (quotientSystem I f F p) :=
  limit.lift (quotientSystem I f F p)
    { pt := GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p
      π :=
        { app := fun n ↦ toQuotientCohomology I f F p n.unop
          naturality := fun {sourceIndex targetIndex} g ↦
            toLimit_naturality I f F p sourceIndex targetIndex g } }

/-- Projecting `toLimit` to stage `n` recovers `toQuotientCohomology`. -/
theorem toLimit_comp_π (I : Ideal A)
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (F : X.Modules)
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p n : ℕ) :
    toLimit I f F p ≫ limit.π (quotientSystem I f F p) (op n) =
      toQuotientCohomology I f F p n :=
  limit.lift_π _ _

/-- Over an I-adically complete Noetherian ring, the canonical comparison from
cohomology of a coherent sheaf on a proper algebraic space to the inverse limit
of its ideal-power quotient cohomology is an isomorphism in every degree. -/
@[stacks 08B0]
instance isIso_toLimit [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) [Proper f]
    (F : X.Modules) [F.IsCoherent]
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
    [HasInjectiveResolutions X.Modules] (p : ℕ) :
    IsIso (toLimit I f F p) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology
