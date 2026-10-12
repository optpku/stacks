/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Symmetric.Lift
public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.Construction

/-!
# Zero sections of relative spectra

This file characterizes the zero section of a chosen relative-spectrum model
of the symmetric algebra of a quasicoherent module.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeSpectrumOver

variable {S : Scheme.{u}} {M : S.Modules} [M.IsQuasicoherent]

/-- A morphism from the base to a chosen relative spectrum of `Symm(M)` is a
zero section when it lies over the identity and its induced algebra point
kills every degree-one generator. -/
def IsZeroSection
    (hM : M.IsQuasicoherent)
    (P : RelativeSpectrumOver (@SymmetricAlgebra.qcAlgebra S M hM))
    (z : S ⟶ P.scheme) : Prop :=
  z ≫ P.π = 𝟙 S ∧
    ∀ (U : (Opens S)ᵒᵖ) (x : M.val.obj U),
      (((P.universalMap ≫ relativeSpectrumPairTargetMap P.π z).right.hom.app U).hom
        ((@SymmetricAlgebra.ι S M hM).val.app U x)) = 0

/-- A section of a symmetric-algebra relative spectrum is the zero section
exactly when it lies over the identity and kills the degree-one generators. -/
theorem isZeroSection_iff
    (hM : M.IsQuasicoherent)
    (P : RelativeSpectrumOver (@SymmetricAlgebra.qcAlgebra S M hM))
    (z : S ⟶ P.scheme) :
    IsZeroSection hM P z ↔
      z ≫ P.π = 𝟙 S ∧
        ∀ (U : (Opens S)ᵒᵖ) (x : M.val.obj U),
          (((P.universalMap ≫ relativeSpectrumPairTargetMap P.π z).right.hom.app U).hom
            ((@SymmetricAlgebra.ι S M hM).val.app U x)) = 0 := sorry

end AlgebraicGeometry.Scheme.RelativeSpectrumOver
