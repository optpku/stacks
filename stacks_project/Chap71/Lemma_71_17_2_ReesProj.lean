/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Rees.Blowup
public import ReasLib.RingTheory.ReesAlgebra.BlowupChart
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_18_6_Site
public import stacks_project.Chap67.Lemma_67_14_1_Quotient

/-!
# Type-`u` Rees projective spectrum of an affine étale restriction

On an affine scheme étale over an algebraic space, a quasi-coherent ideal sheaf
restricts to an ideal of global functions. The associated Rees algebra is a
graded ring in `Type u`, so its homogeneous spectrum is an ordinary scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Blowup

/-- The ideal of global functions on an affine étale chart corresponding to the
restriction of a quasi-coherent ideal sheaf. -/
def correspondingIdeal {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (U : affineEtaleSite X) :
    Ideal Γ(U.obj.left.left, ⊤) :=
  IdealSheaf.sections (Modules.toCommSubobject I) (op U.obj)

/-- `correspondingIdeal I U` is the section ideal of `I` on the underlying étale
object of `U`. -/
theorem correspondingIdeal_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (U : affineEtaleSite X) :
    correspondingIdeal I U =
      IdealSheaf.sections (Modules.toCommSubobject I) (op U.obj) :=
  sorry

/-- Membership in `correspondingIdeal I U` is membership in the section ideal of
`I` on the underlying étale object of `U`. -/
theorem mem_correspondingIdeal {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (U : affineEtaleSite X)
    (x : Γ(U.obj.left.left, ⊤)) :
    x ∈ correspondingIdeal I U ↔
      x ∈ IdealSheaf.sections (Modules.toCommSubobject I) (op U.obj) :=
  sorry

/-- The homogeneous spectrum of the Rees algebra of `correspondingIdeal I U`. -/
abbrev reesProj {S : Scheme.{u}} {X : AlgebraicSpace S} (I : IdealSubobject X)
    (U : affineEtaleSite X) : Scheme.{u} :=
  Proj (ReesAlgebra.Grading.grade (correspondingIdeal I U))

/-- `reesProj I U` is `Proj` of the canonical grading of the Rees algebra of
`correspondingIdeal I U`. -/
theorem reesProj_eq {S : Scheme.{u}} {X : AlgebraicSpace S} (I : IdealSubobject X)
    (U : affineEtaleSite X) :
    reesProj I U = Proj (ReesAlgebra.Grading.grade (correspondingIdeal I U)) :=
  sorry

/-- The structure morphism of `reesProj I U` over the affine étale chart `U`. -/
def reesProjToU {S : Scheme.{u}} {X : AlgebraicSpace S} (I : IdealSubobject X)
    (U : affineEtaleSite X) : reesProj I U ⟶ U.obj.left.left :=
  ReesProj.toSpec (correspondingIdeal I U) ≫ U.obj.left.left.isoSpec.inv

/-- `reesProjToU` is `ReesProj.toSpec` followed by the inverse of `Scheme.isoSpec`
on the affine étale chart. -/
theorem reesProjToU_comp {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (U : affineEtaleSite X) :
    reesProjToU I U =
      ReesProj.toSpec (correspondingIdeal I U) ≫ U.obj.left.left.isoSpec.inv :=
  sorry

/-- The homogeneous spectrum of the restricted Rees algebra, as a scheme over `S`. -/
def reesProjOver {S : Scheme.{u}} {X : AlgebraicSpace S} (I : IdealSubobject X)
    (U : affineEtaleSite X) : Over S :=
  Over.mk (reesProjToU I U ≫ U.obj.left.hom)

/-- The underlying scheme of `reesProjOver I U` is `reesProj I U`. -/
theorem reesProjOver_left {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (U : affineEtaleSite X) :
    (reesProjOver I U).left = reesProj I U :=
  sorry

/-- The morphism of algebraic spaces over `S` induced by `reesProjToU`. -/
def reesProjOverToU {S : Scheme.{u}} {X : AlgebraicSpace S} (I : IdealSubobject X)
    (U : affineEtaleSite X) :
    ofOver (reesProjOver I U) ⟶ ofOver U.obj.left :=
  ofOverMap (Over.homMk (reesProjToU I U) rfl)

/-- `reesProjOverToU` is `ofOverMap` of the over-morphism induced by `reesProjToU`. -/
theorem reesProjOverToU_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (U : affineEtaleSite X) :
    reesProjOverToU I U = ofOverMap (Over.homMk (reesProjToU I U) rfl) :=
  sorry

/-- The canonical open immersion of the affine blowup chart associated to `a` into
`reesProj I U`. -/
def affineChartι {S : Scheme.{u}} {X : AlgebraicSpace S} (I : IdealSubobject X)
    (U : affineEtaleSite X) (a : correspondingIdeal I U) :
    Spec (.of (affineBlowupChart (correspondingIdeal I U) a)) ⟶ reesProj I U :=
  Proj.awayι (ReesAlgebra.Grading.grade (correspondingIdeal I U))
    (ReesAlgebra.Grading.degreeOne (correspondingIdeal I U) a)
    (ReesAlgebra.Grading.degreeOne_mem (correspondingIdeal I U) a) Nat.zero_lt_one

/-- `affineChartι I U a` is `Proj.awayι` of the degree-one Rees element `a`. -/
theorem affineChartι_eq {S : Scheme.{u}} {X : AlgebraicSpace S} (I : IdealSubobject X)
    (U : affineEtaleSite X) (a : correspondingIdeal I U) :
    affineChartι I U a =
      Proj.awayι (ReesAlgebra.Grading.grade (correspondingIdeal I U))
        (ReesAlgebra.Grading.degreeOne (correspondingIdeal I U) a)
        (ReesAlgebra.Grading.degreeOne_mem (correspondingIdeal I U) a) Nat.zero_lt_one :=
  sorry

/-- The structure morphism of an affine blowup chart over the affine étale chart `U`. -/
def affineChartToU {S : Scheme.{u}} {X : AlgebraicSpace S} (I : IdealSubobject X)
    (U : affineEtaleSite X) (a : correspondingIdeal I U) :
    Spec (.of (affineBlowupChart (correspondingIdeal I U) a)) ⟶ U.obj.left.left :=
  affineChartι I U a ≫ reesProjToU I U

/-- `affineChartToU` is the composite of `affineChartι` with `reesProjToU`. -/
theorem affineChartToU_comp {S : Scheme.{u}} {X : AlgebraicSpace S} (I : IdealSubobject X)
    (U : affineEtaleSite X) (a : correspondingIdeal I U) :
    affineChartToU I U a = affineChartι I U a ≫ reesProjToU I U :=
  sorry

/-- The morphism `Proj(⊕ I_A^d) ⟶ X` induced by the affine étale chart `U`. -/
def reesProjToX {S : Scheme.{u}} {X : AlgebraicSpace S} (I : IdealSubobject X)
    (U : affineEtaleSite X) : ofOver (reesProjOver I U) ⟶ X :=
  reesProjOverToU I U ≫ U.obj.hom

/-- `reesProjToX` is `reesProjOverToU` followed by the étale chart morphism. -/
theorem reesProjToX_comp {S : Scheme.{u}} {X : AlgebraicSpace S} (I : IdealSubobject X)
    (U : affineEtaleSite X) :
    reesProjToX I U = reesProjOverToU I U ≫ U.obj.hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Blowup
