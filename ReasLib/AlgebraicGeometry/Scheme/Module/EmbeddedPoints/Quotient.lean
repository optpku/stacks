/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.RingTheory.Ideal.AssociatedPrime.Embedded.Localization
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.EmbeddedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Module.Support

/-!
# Removing embedded associated points by a quotient

This file records coherent subobjects whose support is nowhere dense relative
to the support of an ambient module and the resulting quotient properties.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open Set TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (F : X.Modules)

/-- A coherent subobject whose support is nowhere dense inside the support of
the ambient module. -/
def IsCoherentNowhereDenseSubobject (K : Subobject F) : Prop :=
  ((K : X.Modules)).IsCoherent ∧
    IsNowhereDense
      (Subtype.val ⁻¹' moduleSupport ((K : X.Modules)) : Set (moduleSupport F))

/-- A subobject is coherent and nowhere dense exactly when its underlying
module is coherent and its support is nowhere dense in the ambient support. -/
theorem isCoherentNowhereDenseSubobject_iff (K : Subobject F) :
    F.IsCoherentNowhereDenseSubobject K ↔
      ((K : X.Modules)).IsCoherent ∧
        IsNowhereDense
          (Subtype.val ⁻¹' moduleSupport ((K : X.Modules)) : Set (moduleSupport F)) :=
  Iff.rfl

/-- The underlying module of a coherent nowhere-dense subobject is coherent. -/
theorem IsCoherentNowhereDenseSubobject.isCoherent {K : Subobject F}
    (hK : F.IsCoherentNowhereDenseSubobject K) :
    ((K : X.Modules)).IsCoherent :=
  hK.1

/-- The support of a coherent nowhere-dense subobject is nowhere dense in the
support of the ambient module. -/
theorem IsCoherentNowhereDenseSubobject.isNowhereDense {K : Subobject F}
    (hK : F.IsCoherentNowhereDenseSubobject K) :
    IsNowhereDense
      (Subtype.val ⁻¹' moduleSupport ((K : X.Modules)) : Set (moduleSupport F)) :=
  hK.2

variable [IsLocallyNoetherian X] [F.IsCoherent]

/-- A coherent module on a locally Noetherian scheme has a maximal coherent
subobject whose support is nowhere dense in the support of the module. -/
theorem exists_maximal_isCoherentNowhereDenseSubobject :
    ∃ K : Subobject F, Maximal (F.IsCoherentNowhereDenseSubobject) K := sorry

/-- The cokernel of a maximal coherent nowhere-dense subobject has the same
support as the ambient module. -/
theorem IsCoherentNowhereDenseSubobject.support_cokernel_eq_of_maximal
    (K : Subobject F)
    (hK : Maximal (F.IsCoherentNowhereDenseSubobject) K) :
    moduleSupport (cokernel K.arrow) = moduleSupport F := sorry

/-- The cokernel of a maximal coherent nowhere-dense subobject has no embedded
associated points. -/
theorem IsCoherentNowhereDenseSubobject.embeddedAssociatedPoints_cokernel_eq_empty_of_maximal
    (K : Subobject F)
    (hK : Maximal (F.IsCoherentNowhereDenseSubobject) K) :
    embeddedAssociatedPoints (cokernel K.arrow) = (∅ : Set X) := sorry

/-- The cokernel of a maximal coherent nowhere-dense subobject agrees with the
ambient module on an open set dense both in the scheme and in the module's
support. -/
theorem IsCoherentNowhereDenseSubobject.exists_denseOpen_restrictIso_cokernel_of_maximal
    (K : Subobject F)
    (hK : Maximal (F.IsCoherentNowhereDenseSubobject) K) :
    ∃ U : X.Opens,
      Dense (U : Set X) ∧
        Dense (Subtype.val ⁻¹' (U : Set X) : Set (moduleSupport F)) ∧
          Nonempty ((cokernel K.arrow).restrict U.ι ≅ F.restrict U.ι) := sorry

/-- A coherent module on a locally Noetherian scheme admits a maximal coherent
nowhere-dense subobject whose cokernel has the same support, has no embedded
associated points, and agrees with the module on an open set dense both in the
scheme and in the module's support. -/
theorem exists_maximal_isCoherentNowhereDenseSubobject_with_cokernel_properties :
    ∃ K : Subobject F,
      Maximal (F.IsCoherentNowhereDenseSubobject) K ∧
        moduleSupport (cokernel K.arrow) = moduleSupport F ∧
          embeddedAssociatedPoints (cokernel K.arrow) = (∅ : Set X) ∧
            ∃ U : X.Opens,
              Dense (U : Set X) ∧
                Dense (Subtype.val ⁻¹' (U : Set X) : Set (moduleSupport F)) ∧
                  Nonempty ((cokernel K.arrow).restrict U.ι ≅ F.restrict U.ι) := sorry

end AlgebraicGeometry.Scheme.Modules
