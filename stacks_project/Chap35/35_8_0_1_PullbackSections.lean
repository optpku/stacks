/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.PullbackSections

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (ℱ : S.Modules) {A B C : Over S}
  (φ : A ⟶ B) (ψ : B ⟶ C)

#check (AlgebraicGeometry.Scheme.Modules.PullbackSections.map ℱ φ :
  Scheme.Modules.globalSections ((Scheme.Modules.pullback B.hom).obj ℱ) ⟶
    Scheme.Modules.globalSections ((Scheme.Modules.pullback A.hom).obj ℱ))

#check (AlgebraicGeometry.Scheme.Modules.PullbackSections.map_id ℱ A :
  AlgebraicGeometry.Scheme.Modules.PullbackSections.map ℱ (𝟙 A) =
    𝟙 (Scheme.Modules.globalSections ((Scheme.Modules.pullback A.hom).obj ℱ)))

#check (AlgebraicGeometry.Scheme.Modules.PullbackSections.map_comp ℱ φ ψ :
  AlgebraicGeometry.Scheme.Modules.PullbackSections.map ℱ (φ ≫ ψ) =
    AlgebraicGeometry.Scheme.Modules.PullbackSections.map ℱ ψ ≫
      AlgebraicGeometry.Scheme.Modules.PullbackSections.map ℱ φ)

#check (AlgebraicGeometry.Scheme.Modules.PullbackSections.over S ℱ :
  (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u})

#check (AlgebraicGeometry.Scheme.Modules.PullbackSections.over_obj S ℱ A :
  (AlgebraicGeometry.Scheme.Modules.PullbackSections.over S ℱ).obj (op A) =
    Scheme.Modules.globalSections ((Scheme.Modules.pullback A.hom).obj ℱ))

#check (AlgebraicGeometry.Scheme.Modules.PullbackSections.over_map S ℱ φ :
  (AlgebraicGeometry.Scheme.Modules.PullbackSections.over S ℱ).map φ.op =
    AlgebraicGeometry.Scheme.Modules.PullbackSections.map ℱ φ)
