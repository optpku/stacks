/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Algebra
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Graded.Adjunction
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Graded algebra sheaves and the module pullback-pushforward adjunction

The pullback-pushforward adjunction acts on the underlying graded module of a graded algebra
sheaf degreewise.  This integration leaf exposes the object, map, and Hom-equivalence formulas
without constructing a second adjunction for graded algebras.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.GradedAlgebraSheaf

noncomputable section

universe u v

namespace RingedSite.Hom.Graded.Algebra

section

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪X : Sheaf JC CommRingCat.{max u v}}
variable {𝒪Y : Sheaf JD CommRingCat.{max u v}}
variable (f : RingedSite.ofCommRingSheaf JC 𝒪X ⟶
  RingedSite.ofCommRingSheaf JD 𝒪Y)
variable {ι : Type} [AddMonoid ι]

/-- The pushforward of the underlying graded object of a graded algebra sheaf is computed
degreewise by module pushforward. -/
@[stacks 0FQX]
theorem pushforward_obj_apply (𝒜 : GradedAlgebraSheaf 𝒪X ι) (n : ι) :
    ((Graded.pushforward f).obj ((forgetToGraded 𝒪X ι).obj 𝒜)) n =
      f.modulePushforward.obj (𝒜 n) := sorry

/-- Pushforward of a morphism of underlying graded algebra objects is computed degreewise. -/
@[stacks 0FQX]
theorem pushforward_map_apply {𝒜 ℬ : GradedAlgebraSheaf 𝒪X ι}
    (φ : 𝒜 ⟶ ℬ) (n : ι) :
    ((Graded.pushforward f).map ((forgetToGraded 𝒪X ι).map φ)) n =
      f.modulePushforward.map (φ.hom n) := sorry

variable [HasWeakSheafify JC AddCommGrpCat.{max u v}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [(PresheafOfModules.pushforward.{max u v}
  f.structureSheafMap.hom).IsRightAdjoint]

/-- The pullback of the underlying graded object of a graded algebra sheaf is computed
degreewise by module pullback. -/
@[stacks 0FQX]
theorem pullback_obj_apply (ℬ : GradedAlgebraSheaf 𝒪Y ι) (n : ι) :
    ((Graded.pullback f).obj ((forgetToGraded 𝒪Y ι).obj ℬ)) n =
      f.modulePullback.obj (ℬ n) := sorry

/-- Pullback of a morphism of underlying graded algebra objects is computed degreewise. -/
@[stacks 0FQX]
theorem pullback_map_apply {𝒜 ℬ : GradedAlgebraSheaf 𝒪Y ι}
    (φ : 𝒜 ⟶ ℬ) (n : ι) :
    ((Graded.pullback f).map ((forgetToGraded 𝒪Y ι).map φ)) n =
      f.modulePullback.map (φ.hom n) := sorry

/-- On underlying graded objects of graded algebra sheaves, the graded module Hom equivalence
is the ordinary module pullback-pushforward Hom equivalence in every degree. -/
@[stacks 0FQX]
theorem homEquiv_apply_apply (ℬ : GradedAlgebraSheaf 𝒪Y ι)
    (𝒜 : GradedAlgebraSheaf 𝒪X ι)
    (g : (Graded.pullback f).obj ((forgetToGraded 𝒪Y ι).obj ℬ) ⟶
      (forgetToGraded 𝒪X ι).obj 𝒜) (n : ι) :
    (Graded.homEquiv f ((forgetToGraded 𝒪Y ι).obj ℬ)
      ((forgetToGraded 𝒪X ι).obj 𝒜) g) n =
        f.modulePullbackHomEquiv (ℬ n) (𝒜 n) (g n) := sorry

end

end RingedSite.Hom.Graded.Algebra

end
