/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Lift.Gerbe
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FirstOrderThickening
public import ReasLib.CategoryTheory.Fibered.Gerbe.Band
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.GerbeDescent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Abelian automorphisms and quasi-coherent bands of first-order lifts
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open Functor.IsFibered.InGroupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Lift

variable {S : Scheme.{u}} {X X' : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack X']
variable (iX : X ⟶ X') [IsThickening iX]
variable {W : AlgebraicSpace S} (x : W.toGroupoids ⟶ X)
variable [Groupoids.Hom.Smooth x]

/-- The automorphism sheaves in the gerbe of cartesian smooth lifts across a
first-order thickening of algebraic stacks are abelian. -/
instance instAutomorphismIsAbelian [IsFirstOrderThickening iX] :
    Automorphism.IsAbelian (p iX x) := sorry

/-- Every additive band of the gerbe of cartesian smooth lifts across a first-order
thickening admits a quasi-coherent module structure whose underlying additive sheaf,
extended from the small étale site to the spaces-étale site, is isomorphic to that band. -/
theorem exists_quasicoherentBandModule [IsFirstOrderThickening iX]
    (G : Sheaf (AlgebraicSpace.spacesEtaleTopology W) AddCommGrpCat.{u + 1})
    (hG : IsBand (p iX x) (AlgebraicSpace.spacesEtaleTopology W) G) :
    ∃ M : RingedSite.ModuleCat.{u + 1} (AlgebraicSpace.commRingedSiteLift W),
      M.IsQuasicoherent ∧
        Nonempty ((AlgebraicSpace.GerbeModuleDescent.additiveExtension W).obj
          ((SheafOfModules.toSheaf (AlgebraicSpace.commRingedSiteLift W).structureSheaf).obj M)
            ≅ G) := sorry

end AlgebraicGeometry.AlgebraicStack.Lift
