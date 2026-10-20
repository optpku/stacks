/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.InternalHom.Derived.Cohomology.Resolution
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u v

open CategoryTheory DifferentialGradedBimodule
open DifferentialGradedBimodule.InternalHom.Derived.Cohomology

variable {R : Type u} [CommRing R]
variable {A B : CochainDGAlgebra.{u, v} R}
variable (T : DifferentialGradedBimodule A B)
variable (M : DifferentialGradedModule B)
variable (I : DifferentialGradedModule.PropertyI.Resolution B M) (n : ℤ)

/- Lemma 22.31.4 (0CS5): a property-I resolution computes internal-Hom cohomology as shifted
morphisms in the derived category of right DG `B`-modules. -/
@[stacks 0CS5]
#check
  (Resolution.linearEquiv T I n :
    (internalHom T I.obj).homology n ≃ₗ[R]
      ((DifferentialGradedModule.Derived.Q B).obj
          ((DifferentialGradedModule.toK B).obj T.toRightModule) ⟶
        ((DifferentialGradedModule.Derived.Q B).obj
          ((DifferentialGradedModule.toK B).obj M))⟦n⟧))

/- The source-independent bifunctorial formulation is a companion library interface. -/
#check uliftSourceBifunctorIso A B n

/- A property-I resolution is the reusable computational specialization of the natural
bifunctorial statement. -/
#check @Resolution.linearEquiv

/- The reusable model layer identifies the chosen property-I resolution with the abstract
derived internal-Hom object before taking cohomology. -/
#check @InternalHom.Derived.Resolution.modelIso
#check @Resolution.iso

/- Compatible strict maps of property-I resolutions compose, and both the model and cohomology
comparisons are natural in such maps. -/
#check @DifferentialGradedModule.PropertyI.Resolution.Map
#check @InternalHom.Derived.Resolution.modelIso_hom_naturality_source
#check @InternalHom.Derived.Resolution.modelIso_hom_naturality_target
#check @Resolution.iso_hom_naturality_source
#check @Resolution.iso_hom_naturality_target

/- Canonical comparisons through the abstract derived value make the result independent of the
chosen property-I resolution, without choosing a strict comparison map. -/
#check @InternalHom.Derived.Resolution.comparisonIso
#check @Resolution.comparisonIso
#check @Resolution.comparisonLinearEquiv

/- The model-based equivalence agrees with the direct K-injective construction. -/
#check @Resolution.linearEquiv_eq_direct

/- The reusable formulation removes the chosen resolution from the public surface and is natural
in the derived target. -/
#check @linearEquiv
#check @uliftIso_naturality_target

/- The functorial formulation uses the canonical universe lift required by derived morphisms. -/
#check @uliftIso

/- The strongest library-facing form is defined on the opposite derived bimodule category and
is covariantly natural in the derived target. -/
#check @uliftBifunctorIso

/- On strict representatives, both sides expose canonical objectwise comparisons with the
fixed-source formulation. -/
#check @uliftBifunctorObjIso
#check @shiftedHomBifunctorObjIso
#check @uliftBifunctorIso_hom_app

/- Pullback along the strict-bimodule localization recovers the strict-source comparison. -/
#check @uliftBifunctorIso_fromBimodules
