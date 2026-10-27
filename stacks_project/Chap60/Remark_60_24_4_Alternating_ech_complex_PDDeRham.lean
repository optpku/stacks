/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.RingTheory.Kaehler.DeRham.Exterior
public import ReasLib.RingTheory.Kaehler.DeRham.DividedPowers.SquareZero
public import ReasLib.RingTheory.Kaehler.DeRham.DividedPowers.Calculus

@[expose] public section
universe u
namespace CrystallinePDDeRham
variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable {J : Ideal B} (δ : DividedPowers J)

#check (CrystallinePDDeRham.relations A B δ : Submodule B Ω[B⁄A])
#check (CrystallinePDDeRham.derivation A B δ :
  Derivation A B (Ω[B⁄A] ⧸ CrystallinePDDeRham.relations A B δ))

#check (CrystallinePDDeRham.algebraicFamily A B : DifferentialOperator.DeRham.Family A B Ω[B⁄A])

end CrystallinePDDeRham
