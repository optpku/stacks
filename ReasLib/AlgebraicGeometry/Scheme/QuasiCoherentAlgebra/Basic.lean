/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite

/-!
# Quasi-coherent algebra sheaves on schemes

This file defines the category of quasi-coherent algebra objects over a
scheme. It is independent of any particular relative-spectrum or graded
algebra construction.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open SheafOfModules.RingedSite

universe u

namespace AlgebraicGeometry.Scheme

/-- The commutative structure sheaf of a scheme, with its ambient sheaf type made explicit. -/
abbrev schemeCommRingSheaf (S : Scheme.{u}) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology S) CommRingCat.{u} :=
  S.sheaf

/-- The property of an `𝒪_S`-algebra whose underlying `𝒪_S`-module is quasi-coherent. -/
abbrev qcAlgebraUnderProperty (S : Scheme.{u}) :
    ObjectProperty (Under (schemeCommRingSheaf S)) :=
  fun A ↦
    ((restrictionAlong A.hom).obj
      (unitModule (Opens.grothendieckTopology S)
        (A.right : CategoryTheory.Sheaf
          (Opens.grothendieckTopology S) CommRingCat.{u}))).IsQuasicoherent

/-- The category of quasi-coherent `𝒪_S`-algebras. -/
abbrev QcAlgebraUnder (S : Scheme.{u}) :=
  (qcAlgebraUnderProperty S).FullSubcategory

namespace QcAlgebraUnder

/-- The forgetful functor from quasi-coherent `𝒪_S`-algebras to all `𝒪_S`-algebras. -/
abbrev forget (S : Scheme.{u}) : S.QcAlgebraUnder ⥤ Under (schemeCommRingSheaf S) :=
  (qcAlgebraUnderProperty S).ι

/-- The module underlying a quasi-coherent `𝒪_S`-algebra is quasi-coherent. -/
theorem isQuasicoherent_restrictedUnit (S : Scheme.{u}) (A : S.QcAlgebraUnder) :
    ((restrictionAlong A.obj.hom).obj
      (unitModule (Opens.grothendieckTopology S)
        (A.obj.right : CategoryTheory.Sheaf (Opens.grothendieckTopology S) CommRingCat.{u}))).IsQuasicoherent :=
  A.property

end QcAlgebraUnder

end AlgebraicGeometry.Scheme
