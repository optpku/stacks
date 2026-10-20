/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StructureSheaf.CommRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Basic

/-!
# Commutative structure sheaf on the small étale site of an algebraic space

The structure sheaf `𝒪_X` is the global-sections functor `U ↦ Γ(U, 𝒪_U)`, retained as a
sheaf of commutative rings so that tensor products and internal Hom of `𝒪_X`-modules are the
canonical ringed-site operations.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The small étale site of `X`, equipped with its commutative structure sheaf. -/
abbrev commRingedSite {S : Scheme.{u}} (X : AlgebraicSpace S) :
    RingedSite.{u + 1, u, u} :=
  RingedSite.ofCommRingSheaf (smallEtaleTopology X) (commStructureSheaf X)

/-- The structure sheaf of `commRingedSite X` is the underlying ring sheaf of `𝒪_X`. -/
theorem commRingedSite_structureSheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (commRingedSite X).structureSheaf =
      CategoryTheory.Sheaf.ringSheafOfComm (commStructureSheaf X) :=
  rfl

/-- The small étale site of `X`, equipped with the universe-lifted commutative structure sheaf. -/
abbrev commRingedSiteLift {S : Scheme.{u}} (X : AlgebraicSpace S) :
    RingedSite.{u + 1, u, u + 1} :=
  RingedSite.ofCommSheafMax (smallEtaleTopology X) (commStructureSheafLift X)

end AlgebraicGeometry.AlgebraicSpace
