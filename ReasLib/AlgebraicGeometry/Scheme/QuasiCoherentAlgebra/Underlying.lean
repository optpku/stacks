/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Basic

/-!
# Underlying modules of quasi-coherent algebras

This file exposes the sheaf and module underlying a quasi-coherent algebra on a scheme, together
with the map on underlying modules induced by an algebra morphism.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.QcAlgebraUnder

variable (S : Scheme.{u})

/-- The ambient commutative-ring sheaf underlying a quasi-coherent algebra on `S`. -/
abbrev sheaf (A : S.QcAlgebraUnder) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology S) CommRingCat.{u} :=
  (A.obj.right : CategoryTheory.Sheaf (Opens.grothendieckTopology S) CommRingCat.{u})

/-- The `ᵊa_S`-module underlying a quasi-coherent `ᵊa_S`-algebra. -/
abbrev underlyingModule (A : S.QcAlgebraUnder) : S.Modules :=
  (restrictionAlong A.obj.hom).obj
    (unitModule (Opens.grothendieckTopology S) (sheaf S A))

/-- The map of underlying `ᵊa_S`-modules induced by a morphism of quasi-coherent
`ᵊa_S`-algebras. -/
abbrev underlyingModuleMap {A B : S.QcAlgebraUnder} (f : A ⟶ B) :
    underlyingModule S A ⟶ underlyingModule S B := by
  let alpha := ((forget S).map f).right
  let raw :
      SheafOfModules.unit (ringSheaf (Opens.grothendieckTopology S) (sheaf S A)) ⟶
        (restrictionAlong ((forget S).map f).right).obj
          (SheafOfModules.unit (ringSheaf (Opens.grothendieckTopology S) (sheaf S B))) := by
    let rawPush :=
      SheafOfModules.unitToPushforwardObjUnit
        (SheafOfModules.ChangeOfRings.homOverId
          (ringSheafMap (J := Opens.grothendieckTopology S) alpha))
    exact rawPush ≫
      (SheafOfModules.ChangeOfRings.pushforwardIso
        (ringSheafMap (J := Opens.grothendieckTopology S) alpha)).hom.app
        (SheafOfModules.unit (ringSheaf (Opens.grothendieckTopology S) (sheaf S B)))
  have hcomp : A.obj.hom ≫ ((forget S).map f).right = B.obj.hom := by
    simpa using (((forget S).map f).w).symm
  let raw :
      underlyingModule S A ⟶
        (restrictionAlong (A.obj.hom ≫ ((forget S).map f).right)).obj
          (unitModule (Opens.grothendieckTopology S) (sheaf S B)) :=
    (restrictionAlong A.obj.hom).map raw
  simpa [underlyingModule] using hcomp ▸ raw

end AlgebraicGeometry.Scheme.QcAlgebraUnder
