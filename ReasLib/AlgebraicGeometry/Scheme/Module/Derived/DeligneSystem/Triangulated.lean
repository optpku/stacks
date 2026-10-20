/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.DeligneSystem.ProExtension

/-!
# Distinguished triangles of Deligne systems

This module relates positive inverse systems of distinguished triangles to the pro-objects
presented by Deligne systems.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.Bounded.CohomologyIn
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe v

namespace AlgebraicGeometry.Scheme.ModuleDerived

variable {X U : Scheme.{v}} {j : U ⟶ X}
variable [IsNoetherian X] [IsNoetherian U] [IsOpenImmersion j]

/-- The pro-object in the ambient derived category presented by a positive inverse system of
bounded complexes with coherent cohomology. -/
noncomputable abbrev boundedProObject
    (K : PNatInverseSystem Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]) :
    Pro (DerivedCategory X.Modules) :=
  (@Pro.lim (DerivedCategory X.Modules) _ (OrderDual ℕ+) _ _ _ _).obj
    (K ⋙ ambient (SheafOfModules.isCoherent X.ringCatSheaf))

/-- In a positive inverse system of distinguished triangles of bounded coherent complexes,
if the first and third systems present pro-objects of Deligne systems, then so does the second
system. -/
theorem exists_proIso_middle_of_distinguished
    (K L M : PNatInverseSystem
      Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf])
    (T : PNatInverseSystem (Pretriangulated.Triangle (DerivedCategory X.Modules)))
    (eK : T ⋙ Pretriangulated.Triangle.π₁ ≅
      K ⋙ ambient (SheafOfModules.isCoherent X.ringCatSheaf))
    (eL : T ⋙ Pretriangulated.Triangle.π₂ ≅
      L ⋙ ambient (SheafOfModules.isCoherent X.ringCatSheaf))
    (eM : T ⋙ Pretriangulated.Triangle.π₃ ≅
      M ⋙ ambient (SheafOfModules.isCoherent X.ringCatSheaf))
    (hT : ∀ n : ℕ+, T.stage n ∈
      Pretriangulated.distinguishedTriangles)
    (hK : ∃ S : DeligneSystem j,
      Nonempty (boundedProObject K ≅ S.proObject))
    (hM : ∃ S : DeligneSystem j,
      Nonempty (boundedProObject M ≅ S.proObject)) :
    ∃ S : DeligneSystem j,
      Nonempty (boundedProObject L ≅ S.proObject) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
