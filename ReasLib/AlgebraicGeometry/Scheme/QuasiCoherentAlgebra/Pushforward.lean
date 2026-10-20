/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Definition

/-!
# Pushforwards of structure sheaves as quasi-coherent algebras

This file bundles the pushforward of the structure sheaf along a quasi-compact,
quasi-separated morphism as a quasi-coherent algebra over the target.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open RingedSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X S : Scheme.{u}}

/-- The pushed-forward structure sheaf `f_* 𝒪_X`, regarded as an `𝒪_S`-algebra, is
quasi-coherent when `f` is quasi-compact and quasi-separated. -/
theorem pushforwardStructureSheaf_isQuasicoherent
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] :
    ((restrictionAlong (RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom)).obj
      (unitModule (Opens.grothendieckTopology S)
        ((TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj X.sheaf))).IsQuasicoherent := sorry

/-- The quasi-coherent `𝒪_S`-algebra underlying the direct image `f_* 𝒪_X`. -/
noncomputable def pushforwardStructureSheafQcAlgebra
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] :
    S.QcAlgebraUnder :=
  ⟨Under.mk (RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom),
    pushforwardStructureSheaf_isQuasicoherent f⟩

/-- The underlying algebra of `pushforwardStructureSheafQcAlgebra f` is the raw
pushed-forward structure sheaf algebra. -/
theorem pushforwardStructureSheafQcAlgebra_obj
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] :
    (pushforwardStructureSheafQcAlgebra f).obj =
      Under.mk (RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom) := sorry

end AlgebraicGeometry.Scheme
