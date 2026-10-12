/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Parasitic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.StructureSheaf

/-!
# Parasitic sheaves of modules on standard big sites

This module defines flat-objectwise vanishing for module sheaves on standard
big sites and provides its basic specification and transport API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u z

namespace SheafOfModules

variable {S : Scheme.{u}} {τ : StandardTopology}

/-- A sheaf of modules on the standard big `τ`-site is parasitic one when it
vanishes on every scheme flat over the base. -/
def IsParasiticOne
    (ℱ : RingedSite.ModuleCat.{z} (StandardTopology.Big.ringedSite τ S)) : Prop :=
  ∀ U : Over S, Flat U.hom → IsZero (ℱ.val.obj (op U))

/-- The flat-objectwise characterization of a parasitic-one module sheaf. -/
theorem isParasiticOne_iff
    (ℱ : RingedSite.ModuleCat.{z} (StandardTopology.Big.ringedSite τ S)) :
    IsParasiticOne ℱ ↔
      ∀ U : Over S, Flat U.hom → IsZero (ℱ.val.obj (op U)) := sorry

namespace IsParasiticOne

/-- A parasitic-one module sheaf vanishes on a specified flat scheme over the
base. -/
theorem isZero
    {ℱ : RingedSite.ModuleCat.{z} (StandardTopology.Big.ringedSite τ S)}
    (hℱ : IsParasiticOne ℱ) (U : Over S) (hU : Flat U.hom) :
    IsZero (ℱ.val.obj (op U)) := sorry

end IsParasiticOne

/-- The parasitic-one property for module sheaves is invariant under
isomorphism. -/
theorem isParasiticOne_iff_of_iso
    {ℱ 𝒢 : RingedSite.ModuleCat.{z} (StandardTopology.Big.ringedSite τ S)}
    (e : ℱ ≅ 𝒢) : IsParasiticOne ℱ ↔ IsParasiticOne 𝒢 := sorry

/-- At the scheme universe, the sheaf and presheaf formulations of
parasitic-one agree. -/
theorem isParasiticOne_iff_presheaf
    (ℱ : RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S)) :
    IsParasiticOne ℱ ↔ PresheafOfModules.IsParasiticOne ℱ.val := sorry

end SheafOfModules
