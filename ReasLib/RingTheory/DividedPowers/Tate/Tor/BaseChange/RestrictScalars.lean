/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.RestrictScalars.Homology
public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.RestrictScalars
public import ReasLib.RingTheory.DividedPowers.Tate.Tor.BaseChange

/-!
# Restricted base-change homology as Tor

For a supplied scalar-extension model of a Tate resolution, the restricted natural complex and
the natural complex of the restricted divided-power chain DGA have canonically identified
homology.  Composing this comparison with the Tate computation gives a degreewise linear
equivalence from model homology to the canonical Mathlib `Tor` objects.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace TateResolution.BaseChange

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]
variable {J : Type v} {pi0 : MvPolynomial J R →ₐ[R] T}
variable (A : TateResolution.{u, v} pi0)

/-- The divided-power chain DGA of a supplied base-change model, restricted to the base ring. -/
abbrev restrictedAlgebra
    (Y : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra) :
    DividedPowerChainAlgebra R :=
  DividedPowerChainAlgebra.restrictScalars (algebraMap R S) Y.algebra

/-- Tag 09PQ: the canonical Tor object is the integer homology of the restricted divided-power
chain DGA underlying a supplied base-change model. -/
@[stacks 09PQ "restricted Tate base-change homology as Tor"]
noncomputable def torHomologyIso
    (Y : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra) (n : ℕ) :
    (((CategoryTheory.Tor (ModuleCat R) n).obj (ModuleCat.of R S)).obj
        (ModuleCat.of R T)) ≅
      (restrictedAlgebra A Y).toChainDGAlgebra.homology (n : ℤ) :=
  homologyIso A Y n ≪≫
    ModuleCat.restrictScalarsHomologyIso (algebraMap R S)
      Y.algebra.toChainDGAlgebra.natRestriction n ≪≫
    (ModuleCat.restrictScalars (algebraMap R S)).mapIso
      (Y.algebra.toChainDGAlgebra.natRestrictionHomologyIso n) ≪≫
    (ChainDGAlgebra.RestrictScalars.homologyIso (algebraMap R S)
      Y.algebra.toChainDGAlgebra (n : ℤ)).symm

/-- The degreewise linear equivalence from restricted model homology to the canonical Tor
module.  This is the orientation consumed by graded-algebra transport. -/
@[stacks 09PQ "degreewise transport from restricted Tate homology to Tor"]
noncomputable def homologyTorEquiv
    (Y : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra) (n : ℕ) :
    (restrictedAlgebra A Y).toChainDGAlgebra.homologyPiece n ≃ₗ[R]
      (((CategoryTheory.Tor (ModuleCat R) n).obj (ModuleCat.of R S)).obj
        (ModuleCat.of R T)) :=
  (torHomologyIso A Y n).symm.toLinearEquiv

/-- The forward Tor-to-homology map is the composite of the four canonical comparison maps. -/
theorem torHomologyIso_hom
    (Y : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra) (n : ℕ) :
    (torHomologyIso A Y n).hom =
      (homologyIso A Y n).hom ≫
        (ModuleCat.restrictScalarsHomologyIso (algebraMap R S)
          Y.algebra.toChainDGAlgebra.natRestriction n).hom ≫
        (ModuleCat.restrictScalars (algebraMap R S)).map
          (Y.algebra.toChainDGAlgebra.natRestrictionHomologyIso n).hom ≫
        (ChainDGAlgebra.RestrictScalars.homologyIso (algebraMap R S)
          Y.algebra.toChainDGAlgebra (n : ℤ)).inv := sorry

/-- The model-homology-to-Tor equivalence is inverse to `torHomologyIso`. -/
@[simp]
theorem homologyTorEquiv_apply
    (Y : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra) (n : ℕ)
    (x : (restrictedAlgebra A Y).toChainDGAlgebra.homologyPiece n) :
    homologyTorEquiv A Y n x = (torHomologyIso A Y n).inv x := sorry

end TateResolution.BaseChange
