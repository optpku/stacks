/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Connection
import ReasLib.AlgebraicGeometry.Crystalline.DeRham
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf
open CrisModuleSheaf
open scoped AlgebraicGeometry

@[expose] public section

universe u

variable {S : Scheme.{u}} {I : S.IdealSheafData}
variable {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
variable {h_compatible :
    ∀ (V : S.affineOpens) (f : Γ(S, V)),
      (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
        (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
variable {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}

/- Lemma 60.15.1: A crystal of modules carries its canonical integrable
connection with values in divided-power relative differentials. -/
@[stacks 07J6] #check (canonicalConnection_isIntegrable :
    ∀ (F : CrisModuleSheaf S I γ h_compatible X x₀) [CrisModuleSheaf.IsCrystal F]
      (T : smallCrystallineSite S I γ h_compatible X x₀),
    SheafOfModules.RingedSite.Connection.IsIntegrable.{u, u}
      (CrystallineModuleSheaf.CrisModuleSheaf.canonicalConnection F T)
      (CrystallineModuleSheaf.CrisModuleSheaf.exteriorCalculus T))

end
