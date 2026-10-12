/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeProjFromSections

/-!
# Degree-one maps from relative projective section data

This module records when a multiplicative section homomorphism admits an epic degree-one map
from the pulled-back degree-one piece to its underlying invertible module.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeProjTwist.Hom

variable {S X : Scheme.{u}} {f : X ⟶ S} {L : X.Modules}
variable [hL : Scheme.Modules.Invertible L]
variable {𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf}

/-- A multiplicative section homomorphism has an epic degree-one adjoint when there is an epic
map from the pulled-back first graded piece to the invertible module whose adjoint is the first
component of the homomorphism, after the canonical degree-one identifications. -/
def HasEpicDegreeOneAdjoint
    (ψ : Scheme.RelativeProjTwist.Hom 𝒜 f
      (@RingedSpace.InvertiblePower.gradedAlgebra _ L
        (Scheme.Modules.Invertible.ringedSpaceIsInvertible hL))) : Prop :=
  ∃ degreeOneMap : (Scheme.Modules.pullback f).obj (𝒜 (Int.ofNat 1)) ⟶ L,
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv
        (𝒜 (Int.ofNat 1)) L degreeOneMap =
      ψ.hom 1 ≫
        (Scheme.Modules.pushforward f).map
          ((@RingedSpace.InvertiblePower.natIso _ L
            (Scheme.Modules.Invertible.ringedSpaceIsInvertible hL) 1).inv ≫
              (RingedSpace.TensorPower.oneIso L).hom) ∧
      Epi degreeOneMap

/-- Having an epic degree-one adjoint is exactly the existence of a map satisfying the stated
adjunction equation and epimorphy condition. -/
theorem hasEpicDegreeOneAdjoint_iff
    (ψ : Scheme.RelativeProjTwist.Hom 𝒜 f
      (@RingedSpace.InvertiblePower.gradedAlgebra _ L
        (Scheme.Modules.Invertible.ringedSpaceIsInvertible hL))) :
    HasEpicDegreeOneAdjoint ψ ↔
      ∃ degreeOneMap : (Scheme.Modules.pullback f).obj (𝒜 (Int.ofNat 1)) ⟶ L,
        (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv
            (𝒜 (Int.ofNat 1)) L degreeOneMap =
          ψ.hom 1 ≫
            (Scheme.Modules.pushforward f).map
              ((@RingedSpace.InvertiblePower.natIso _ L
                (Scheme.Modules.Invertible.ringedSpaceIsInvertible hL) 1).inv ≫
                  (RingedSpace.TensorPower.oneIso L).hom) ∧
          Epi degreeOneMap :=
  Iff.rfl

end AlgebraicGeometry.Scheme.RelativeProjTwist.Hom
