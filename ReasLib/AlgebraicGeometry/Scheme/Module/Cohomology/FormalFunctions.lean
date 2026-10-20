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
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.IdealPower.Quotient

/-!
# Formal functions for coherent sheaf cohomology

The canonical comparisons from adic quotients of cohomology to cohomology of
ideal-power quotient sheaves induce a comparison on inverse limits. For a
proper scheme over a Noetherian affine base and a coherent sheaf, this map is
an isomorphism and a homeomorphism for the limit topologies.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ConcreteCategory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.IdealPowerCohomology.Quotient

variable {A : Type u} [CommRing A]
variable {X : Scheme.{u}}
variable [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]

/-- The ideal power `I ^ n` annihilates the image of `Hom.cohomology f F p` in
`cohomology I f F p n`, so it is contained in the kernel of `toQuotient`. -/
theorem pow_smul_le_ker_toQuotient (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p n : ℕ) :
    I ^ n • (⊤ : Submodule A (Hom.cohomology f F p)) ≤
      LinearMap.ker (toQuotient I f F p n).hom :=
  sorry

/-- The descended comparison
`Hom.cohomology f F p ⧸ I ^ n • ⊤ ⟶ cohomology I f F p n`. -/
def toQuotientModPow (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p n : ℕ) :
    ModuleCat.of A
      (Hom.cohomology f F p ⧸ I ^ n • (⊤ : Submodule A (Hom.cohomology f F p))) ⟶
      cohomology I f F p n :=
  ConcreteCategory.ofHom
    ((I ^ n • (⊤ : Submodule A (Hom.cohomology f F p))).liftQ
      ((toQuotient I f F p n).hom :
        Hom.cohomology f F p →ₗ[A] cohomology I f F p n)
      (pow_smul_le_ker_toQuotient I f F p n))

/-- Composing `toQuotientModPow` with the quotient map recovers `toQuotient`. -/
theorem toQuotientModPow_comp_mkQ (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p n : ℕ) :
    (toQuotientModPow I f F p n).hom ∘ₗ
        Submodule.mkQ (I ^ n • (⊤ : Submodule A (Hom.cohomology f F p))) =
      (toQuotient I f F p n).hom :=
  sorry

/-- The descended comparisons are natural with respect to the adic quotient
transitions and the cohomology tower. -/
theorem toQuotientModPow_natural (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p : ℕ) {m n : ℕ} (h : m ≤ n) :
    ModuleCat.ofHom (AdicCompletion.transitionMap I (Hom.cohomology f F p) h) ≫
        toQuotientModPow I f F p m =
      toQuotientModPow I f F p n ≫ transition I f F p h :=
  sorry

/-- Evaluations on the adic completion followed by the descended comparisons
form a natural family of morphisms to the quotient cohomology tower. -/
theorem limitComparison_naturality (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p : ℕ) (m n : ℕᵒᵖ) (g : m ⟶ n) :
    𝟙 (ModuleCat.of A (AdicCompletion I (Hom.cohomology f F p))) ≫
        ConcreteCategory.ofHom
          (((toQuotientModPow I f F p n.unop).hom ∘ₗ
              AdicCompletion.eval I (Hom.cohomology f F p) n.unop) :
            AdicCompletion I (Hom.cohomology f F p) →ₗ[A]
              cohomology I f F p n.unop) =
      ConcreteCategory.ofHom
          (((toQuotientModPow I f F p m.unop).hom ∘ₗ
              AdicCompletion.eval I (Hom.cohomology f F p) m.unop) :
            AdicCompletion I (Hom.cohomology f F p) →ₗ[A]
              cohomology I f F p m.unop) ≫
        (tower I f F p).map g :=
  sorry

/-- The induced map from the I-adic completion of `Hom.cohomology f F p` to the
inverse limit of `n ↦ cohomology I f F p n`. -/
def limitComparison (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p : ℕ) :
    ModuleCat.of A (AdicCompletion I (Hom.cohomology f F p)) ⟶
      limit (tower I f F p) :=
  limit.lift (tower I f F p)
    { pt := ModuleCat.of A (AdicCompletion I (Hom.cohomology f F p))
      π :=
        { app := fun n ↦
            ConcreteCategory.ofHom
              (((toQuotientModPow I f F p n.unop).hom ∘ₗ
                  AdicCompletion.eval I (Hom.cohomology f F p) n.unop) :
                AdicCompletion I (Hom.cohomology f F p) →ₗ[A]
                  cohomology I f F p n.unop)
          naturality := limitComparison_naturality I f F p } }

/-- Projecting `limitComparison` to stage `n` is evaluation on the completion
followed by `toQuotientModPow`. -/
theorem limitComparison_comp_π (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p n : ℕ) :
    limitComparison I f F p ≫ limit.π (tower I f F p) (op n) =
      ConcreteCategory.ofHom
        (((toQuotientModPow I f F p n).hom ∘ₗ
            AdicCompletion.eval I (Hom.cohomology f F p) n) :
          AdicCompletion I (Hom.cohomology f F p) →ₗ[A]
            cohomology I f F p n) :=
  sorry

/-- For a proper morphism to the spectrum of a Noetherian ring and a coherent
sheaf, the canonical comparison from completed cohomology to the inverse limit
of ideal-power quotient cohomology is an isomorphism of modules. -/
theorem isIso_limitComparison [IsNoetherianRing A] (I : Ideal A)
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (F : X.Modules) [F.IsCoherent] (p : ℕ) :
    IsIso (limitComparison I f F p) :=
  sorry

/-- For a proper morphism to the spectrum of a Noetherian ring and a coherent
sheaf, the canonical comparison from completed cohomology to the inverse limit
of ideal-power quotient cohomology is a homeomorphism for the limit topologies. -/
theorem isHomeomorph_limitComparison [IsNoetherianRing A] (I : Ideal A)
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (F : X.Modules) [F.IsCoherent] (p : ℕ) :
    @IsHomeomorph
      (AdicCompletion I (Hom.cohomology f F p))
      (limit (tower I f F p) : ModuleCat A)
      (⨅ n, TopologicalSpace.induced
        (AdicCompletion.eval I (Hom.cohomology f F p) n) ⊥)
      (Functor.limitTopology (tower I f F p))
      (limitComparison I f F p).hom :=
  sorry

/-- The canonical quotient-cohomology maps form a natural family along the
ideal-power quotient cohomology tower. -/
theorem toLimit_naturality (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p : ℕ) (sourceIndex targetIndex : ℕᵒᵖ)
    (transitionMap : sourceIndex ⟶ targetIndex) :
    𝟙 (Hom.cohomology f F p) ≫ toQuotient I f F p targetIndex.unop =
      toQuotient I f F p sourceIndex.unop ≫ (tower I f F p).map transitionMap :=
  sorry

/-- The canonical comparison `H^p(X, F) ⟶ lim_n H^p(X, F / I^n F)` induced by
`toQuotient`. -/
def toLimit (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p : ℕ) :
    Hom.cohomology f F p ⟶ limit (tower I f F p) :=
  limit.lift (tower I f F p)
    { pt := Hom.cohomology f F p
      π :=
        { app := fun n ↦ toQuotient I f F p n.unop
          naturality := toLimit_naturality I f F p } }

/-- Projecting `toLimit` to stage `n` recovers `toQuotient`. -/
theorem toLimit_comp_π (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p n : ℕ) :
    toLimit I f F p ≫ limit.π (tower I f F p) (op n) = toQuotient I f F p n :=
  sorry

/-- Over an I-adically complete Noetherian ring, the canonical comparison from
cohomology of a coherent sheaf on a proper scheme to the inverse limit of its
ideal-power quotient cohomology is an isomorphism in every degree. -/
theorem isIso_toLimit [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (F : X.Modules) [F.IsCoherent] (p : ℕ) :
    IsIso (toLimit I f F p) :=
  sorry

end AlgebraicGeometry.Scheme.Hom.IdealPowerCohomology.Quotient
