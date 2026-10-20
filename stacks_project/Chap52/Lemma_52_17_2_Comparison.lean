/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Sections.Comparison

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/- The canonical sheaf comparison from the restricted tilde sheaf of the section-limit
quotient to each coherent formal-module stage. -/
#check (AlgebraicGeometry.Scheme.CoherentFormalModules.sectionsComparison :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) (n : ℕ),
    (Scheme.Modules.pullback S.U.ι).obj
        (AlgebraicGeometry.tilde (Ideal.PowerQuotient.stage S.I (sectionsLimit S F) n)) ⟶
      (F.obj.obj (op n)).obj)

end AlgebraicGeometry.Scheme.CoherentFormalModules
