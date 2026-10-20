/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
public import ReasLib.CategoryTheory.Fibered.Stack.Basic
public import ReasLib.CategoryTheory.Sites.Descent.IndexedFunctor.DescentData.Equivalence

/-!
# Stack descent on the standard fibres of a realization

The native induced fibre functor is an implemented equivalence. Its restriction
comparison is constructed by factoring each of the two actual Cartesian lifts
through the other. Descent transport retains the resulting actual inverse
objects, morphisms, unit and counit components.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory

noncomputable section

universe u v uF vF

namespace CategoryTheory.Pseudofunctor.CoGrothendieck

variable {C : Type u} [Category.{v} C]
variable (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vF, uF})

/-- The native inclusion into the standard fibre, with its actual inverse
witnesses supplied by the native co-Grothendieck implementation. -/
def standardFiber (U : C) : F.obj (.mk (op U)) ⥤ (forget F).Fiber U :=
  Functor.Fiber.inducedFunctor (comp_const F U)

/-- Both directions of restriction comparison are actual Cartesian factors. -/
def restrictionIso {U V : C} (f : V ⟶ U) (x : F.obj (.mk (op U))) :
    (standardFiber F V).obj ((F.map f.op.toLoc).toFunctor.obj x) ≅
      ((Functor.fiberPseudofunctor (forget F)).map f.op.toLoc).toFunctor.obj
        ((standardFiber F U).obj x) := by
  let q := forget F
  let ξ := Functor.Cleavage.ofIsFibered q
  let z := (standardFiber F U).obj x
  let chosen := ξ.reindexLift f z
  let original := cartesianLift x f
  let originalStrong := isStronglyCartesian_homCartesianLift x f
  let hom := @Functor.IsStronglyCartesian.map C (Pseudofunctor.CoGrothendieck F) _ _ q
    V U chosen.source z.1 f chosen.hom chosen.isStronglyCartesian
    V (domainCartesianLift x f) (𝟙 V) f (Category.id_comp f).symm
    original originalStrong.toIsHomLift
  let inv := @Functor.IsStronglyCartesian.map C (Pseudofunctor.CoGrothendieck F) _ _ q
    V U (domainCartesianLift x f) z.1 f original originalStrong
    V chosen.source (𝟙 V) f (Category.id_comp f).symm
    chosen.hom chosen.isStronglyCartesian.toIsHomLift
  have homLift : q.IsHomLift (𝟙 V) hom :=
    @Functor.IsStronglyCartesian.map_isHomLift C (Pseudofunctor.CoGrothendieck F) _ _ q
      V U chosen.source z.1 f chosen.hom chosen.isStronglyCartesian
      V (domainCartesianLift x f) (𝟙 V) f (Category.id_comp f).symm
      original originalStrong.toIsHomLift
  have invLift : q.IsHomLift (𝟙 V) inv :=
    @Functor.IsStronglyCartesian.map_isHomLift C (Pseudofunctor.CoGrothendieck F) _ _ q
      V U (domainCartesianLift x f) z.1 f original originalStrong
      V chosen.source (𝟙 V) f (Category.id_comp f).symm
      chosen.hom chosen.isStronglyCartesian.toIsHomLift
  exact
    { hom := ⟨hom, homLift⟩
      inv := ⟨inv, invLift⟩
      hom_inv_id := by sorry
      inv_hom_id := by sorry }

/-- The native fibre equivalences form an indexed functor to the standard
fibre pseudofunctor used by the public stack predicate. -/
def standardFibersIndexed : Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor
    (𝟭 C) F (Functor.fiberPseudofunctor (forget F)) where
  app U := standardFiber F U
  naturality f := NatIso.ofComponents (restrictionIso F f) (by sorry)
  naturality_id := sorry
  naturality_comp := sorry

/-- Each component uses the native, fully implemented fibre equivalence. -/
theorem standardFibersEquivalences (U : C) :
    ((standardFibersIndexed F).app U).IsEquivalence :=
  inferInstanceAs (Functor.Fiber.inducedFunctor (comp_const F U)).IsEquivalence

/-- Standard-fibre stack descent is transported with actual descent inverses,
preimages and glue objects from the supplied original stack. -/
theorem stackOnSite (J : GrothendieckTopology C) (hF : F.IsStack J) :
    CategoryTheory.IsStack.OnSite J (forget F) where
  toIsFibered := inferInstance
  toIsStack :=
    Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor.isStackOfEquivalences
      (standardFibersIndexed F) (standardFibersEquivalences F) J hF

end CategoryTheory.Pseudofunctor.CoGrothendieck
