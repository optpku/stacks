/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Functoriality.Abelian
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Pushforward

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline

universe u

variable {p : ℕ} [Fact p.Prime] {S : Scheme.{u}} (I : S.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (h_compatible : ∀ (V : S.affineOpens) (f : Γ(S, V)),
  (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
    (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))

/- The structure sheaf on the generated small crystalline topology. -/
#check (AlgebraicGeometry.Scheme.Crystalline.smallCrystallineStructureSheaf
  I γ h_compatible s x₀ h_p :
  Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) RingCat.{u})
