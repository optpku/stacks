/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Derived.Triangulated

@[expose] public section

open CategoryTheory CategoryTheory.Pretriangulated
open AlgebraicGeometry.RingedSpace.ModuleDerived.Morphism

universe u

namespace AlgebraicGeometry.ChernClass.Derived

variable {X : Scheme.{u}} [noetherian : IsLocallyNoetherian X]
variable (T : Triangle (RingedSpace.ModuleDerived X.toRingedSpace))
variable (hT : T ∈ distTriang (RingedSpace.ModuleDerived X.toRingedSpace))
variable (h1 : RingedSpace.ModuleDerived.IsPerfect T.obj₁)
variable (h2 : RingedSpace.ModuleDerived.IsPerfect T.obj₂)
variable (h3 : RingedSpace.ModuleDerived.IsPerfect T.obj₃)
variable (hfin :
    (∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsEnvelope f ∧
      HasLocallyBoundedFiniteLocallyFree
        ((RingedSpace.modulePullbackDerived f.toShHom).map T.mor₃)) ∨
    HasLocallyBoundedFiniteLocallyFree T.mor₃ ∨
    (∀ C : irreducibleComponents X, IsCompact (C : Set X)) ∨ CompactSpace X)

include noetherian hT h1 h2 h3 hfin

/-- The first vertex of a distinguished perfect triangle on a locally Noetherian
scheme has defined Chern classes when its connecting map admits a locally bounded
finite locally free model after an envelope or on the scheme, or when the scheme
has compact irreducible components or is compact. -/
theorem isDefined_obj₁_of_connecting : IsDefined T.obj₁ := sorry

/-- The second vertex of a distinguished perfect triangle on a locally Noetherian
scheme has defined Chern classes when its connecting map admits a locally bounded
finite locally free model after an envelope or on the scheme, or when the scheme
has compact irreducible components or is compact. -/
theorem isDefined_obj₂_of_connecting : IsDefined T.obj₂ := sorry

/-- The third vertex of a distinguished perfect triangle on a locally Noetherian
scheme has defined Chern classes when its connecting map admits a locally bounded
finite locally free model after an envelope or on the scheme, or when the scheme
has compact irreducible components or is compact. -/
theorem isDefined_obj₃_of_connecting : IsDefined T.obj₃ := sorry

end AlgebraicGeometry.ChernClass.Derived
