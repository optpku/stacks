/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Differentials.Diagonal
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline
open scoped AlgebraicGeometry

@[expose] public section

universe u

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (S : Scheme.{u}) (I : S.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (h_compatible :
    ∀ (V : S.affineOpens) (f : Γ(S, V)),
      (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
        (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
variable (h_I_quasiCoherent : I.toModule.IsQuasicoherent)
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
variable (T T1 : smallCrystallineSite S I γ h_compatible X x₀)
variable (π0 π1 : T1 ⟶ T) (hprod : IsLimit (BinaryFan.mk π0 π1))
variable (Ω_XS : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)

/- Lemma 60.12.5 (1): the full diagonal kernel ideal is preserved by the
divided powers of the distinguished ideal. -/
@[stacks 07J1] #check
  (AlgebraicGeometry.Scheme.Crystalline.Diagonal.isSubDPIdeal π0 π1 hprod :
    ∀ V : T1.obj.1.thickening.affineOpens,
      DividedPowers.IsSubDPIdeal (T1.obj.1.gamma V)
        ((AlgebraicGeometry.Scheme.Crystalline.Diagonal.ideal π0 π1 hprod).ideal V))

/- Lemma 60.12.5 (2): the crystalline differential module is the diagonal
pullback of the divided-power conormal quotient. -/
@[stacks 07J1] #check
  (CrystallineDifferentials.diagonalKernel p S I γ h_compatible
      h_I_quasiCoherent s X x₀ h_p T T1 π0 π1 hprod Ω_XS :
    Ω_XS.module.obj T.obj.1 ≅
      (Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.Crystalline.Diagonal.diag π0 π1 hprod).hom.thickening).obj
        (AlgebraicGeometry.Scheme.Crystalline.Diagonal.quotient π0 π1 hprod))

/- The diagonal kernel is contained in the distinguished ideal. -/
#check (AlgebraicGeometry.Scheme.Crystalline.Diagonal.ideal_le π0 π1 hprod :
  AlgebraicGeometry.Scheme.Crystalline.Diagonal.ideal π0 π1 hprod ≤ T1.obj.1.ideal)
