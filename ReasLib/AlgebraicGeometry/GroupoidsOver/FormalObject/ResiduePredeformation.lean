/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.Predeformation
public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.Basic

/-!
# Formal objects in the residue-point predeformation category

Concrete specializations of the adic-system construction to scheme-level formal
objects, retaining their original complete local base and forward system.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.FormalObject

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {X : GroupoidsOver S}

/-- The residue-field structure morphism of the complete local base of a formal object. -/
def residueToS (ξ : FormalObject X) :
    Spec (CommRingCat.of (ResidueField ξ.base.carrier)) ⟶ S :=
  Predeformation.adicResidueToS ξ.base.toS

variable (ξ : FormalObject X)
variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
variable [Algebra Λ ξ.base.carrier] [Module.Finite Λ (ResidueField ξ.base.carrier)]
variable (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
variable (h_toS : Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.carrier)) ≫
  openImmersion = ξ.base.toS)

/-- The residue-point predeformation projection with its morphism universe lifted. -/
def predeformationProjection :=
  -- Local instance justification (proof-local temporary data): The shared predeformation API requires this class proof; the explicit source base stores the identical residue finite-type hypothesis, so transport it only inside this compatibility construction without registering a companion instance.
  letI : LocallyOfFiniteType (Predeformation.adicResidueToS ξ.base.toS) :=
    ξ.base.residue_locallyOfFiniteType
  Predeformation.adicProjection ξ.base.toS ξ.objects ξ.over_obj openImmersion h_toS

/-- A scheme-level formal object yields the formal object of its residue-point predeformation category. -/
def toPredeformation :
    _root_.FormalObject (predeformationProjection ξ openImmersion h_toS) :=
  -- Local instance justification (proof-local temporary data): The shared predeformation API requires this class proof; the explicit source base stores the identical residue finite-type hypothesis, so transport it only inside this compatibility construction without registering a companion instance.
  letI : LocallyOfFiniteType (Predeformation.adicResidueToS ξ.base.toS) :=
    ξ.base.residue_locallyOfFiniteType
  Predeformation.formalObjectOfAdicSystem ξ.base.toS ξ.objects ξ.step ξ.over_obj
    ξ.over_step openImmersion h_toS

end AlgebraicGeometry.GroupoidsOver.FormalObject
