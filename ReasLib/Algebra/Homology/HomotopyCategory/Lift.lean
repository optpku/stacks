/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Descending functors of complexes to homotopy categories

An additive functor on the underlying categories induces a functor on homotopy categories by
mapping complexes degreewise. Some important functors, such as totalization, are already defined
between categories of complexes. For those functors the relevant hypothesis is instead that they
send homotopic maps to homotopic maps.

This file packages that more general quotient construction. It applies to different source and
target complex shapes and exposes the factorization and computation API needed downstream.
-/

@[expose] public section

open CategoryTheory HomologicalComplex

noncomputable section

universe v₁ u₁ v₂ u₂ w₁ w₂ w₃

namespace CategoryTheory.Functor

variable {V : Type u₁} {W : Type u₂} [Category.{v₁} V] [Category.{v₂} W]
  [Preadditive V] [Preadditive W]
  {I : Type w₁} {J : Type w₂} {c : ComplexShape I} {d : ComplexShape J}

/-- A functor between categories of complexes preserves homotopy when it maps the homotopy
relation on every hom-set into the target homotopy relation. -/
def PreservesHomotopy
    (F : HomologicalComplex V c ⥤ HomologicalComplex W d) : Prop :=
  ∀ ⦃K L : HomologicalComplex V c⦄ ⦃f g : K ⟶ L⦄,
    homotopic V c f g → homotopic W d (F.map f) (F.map g)

namespace PreservesHomotopy

/-- Preservation of homotopy is closed under composition. -/
theorem comp
    {U : Type*} [Category* U] [Preadditive U]
    {K : Type w₃} {e : ComplexShape K}
    {F : HomologicalComplex V c ⥤ HomologicalComplex W d}
    {G : HomologicalComplex W d ⥤ HomologicalComplex U e}
    (hF : F.PreservesHomotopy) (hG : G.PreservesHomotopy) :
    (F ⋙ G).PreservesHomotopy := sorry

/-- A naturally isomorphic functor preserves homotopy whenever the other functor does. -/
theorem ofIso
    {F G : HomologicalComplex V c ⥤ HomologicalComplex W d}
    (e : F ≅ G) (hG : G.PreservesHomotopy) :
    F.PreservesHomotopy := sorry

end PreservesHomotopy

namespace Homotopy

/-- A homotopy-preserving functor between categories of complexes descends to their homotopy
categories. -/
@[stacks 0G6D "descent of a homotopy-preserving functor"]
noncomputable def lift
    (F : HomologicalComplex V c ⥤ HomologicalComplex W d)
    (hF : F.PreservesHomotopy) :
    HomotopyCategory V c ⥤ HomotopyCategory W d :=
  Quotient.lift (homotopic V c) (F ⋙ HomotopyCategory.quotient W d)
    (fun _ _ _ _ h ↦ Quotient.sound (homotopic W d) (hF h))

/-- The quotient functor followed by the descended functor is canonically isomorphic to the raw
functor followed by the target quotient. -/
noncomputable def liftFactors
    (F : HomologicalComplex V c ⥤ HomologicalComplex W d)
    (hF : F.PreservesHomotopy) :
    HomotopyCategory.quotient V c ⋙ lift F hF ≅
      F ⋙ HomotopyCategory.quotient W d :=
  Quotient.lift.isLift _ _ _

/-- The canonical localization lifting datum for a homotopy-preserving complex functor. -/
@[stacks 0G6D "homotopy-category localization lifting"]
noncomputable instance liftLifting
    (F : HomologicalComplex V c ⥤ HomologicalComplex W d)
    (hF : F.PreservesHomotopy) :
    Localization.Lifting
      (HomotopyCategory.quotient V c)
      (HomologicalComplex.homotopyEquivalences V c)
      (F ⋙ HomotopyCategory.quotient W d)
      (lift F hF) where
  iso := liftFactors F hF

/-- A natural isomorphism between homotopy-preserving functors descends to a natural
isomorphism between their induced functors on homotopy categories. -/
noncomputable def liftIso
    {F G : HomologicalComplex V c ⥤ HomologicalComplex W d}
    (hF : F.PreservesHomotopy) (hG : G.PreservesHomotopy) (e : F ≅ G) :
    lift F hF ≅ lift G hG :=
  Quotient.natIsoLift (homotopic V c)
    (liftFactors F hF ≪≫ Functor.isoWhiskerRight e (HomotopyCategory.quotient W d) ≪≫
      (liftFactors G hG).symm)

/-- On a quotient object, the descended comparison is the target quotient of the original
comparison component. -/
@[simp]
theorem liftIso_hom_app
    {F G : HomologicalComplex V c ⥤ HomologicalComplex W d}
    (hF : F.PreservesHomotopy) (hG : G.PreservesHomotopy) (e : F ≅ G)
    (K : HomologicalComplex V c) :
    (liftIso hF hG e).hom.app ((HomotopyCategory.quotient V c).obj K) =
      (HomotopyCategory.quotient W d).map (e.hom.app K) := sorry

/-- The descended functor acts on a quotient object by applying the raw functor. -/
@[simp]
theorem lift_obj
    (F : HomologicalComplex V c ⥤ HomologicalComplex W d)
    (hF : F.PreservesHomotopy) (K : HomologicalComplex V c) :
    (lift F hF).obj ((HomotopyCategory.quotient V c).obj K) =
      (HomotopyCategory.quotient W d).obj (F.obj K) := sorry

/-- The descended functor acts on the class of a map by applying the raw functor. -/
@[simp]
theorem lift_map
    (F : HomologicalComplex V c ⥤ HomologicalComplex W d)
    (hF : F.PreservesHomotopy) {K L : HomologicalComplex V c} (f : K ⟶ L) :
    (lift F hF).map ((HomotopyCategory.quotient V c).map f) =
      (HomotopyCategory.quotient W d).map (F.map f) := sorry

/-- Additivity descends along the homotopy quotient. -/
instance liftAdditive
    (F : HomologicalComplex V c ⥤ HomologicalComplex W d)
    (hF : F.PreservesHomotopy) [F.Additive] :
    (lift F hF).Additive := sorry

section Shift

variable (F : CochainComplex V ℤ ⥤ CochainComplex W ℤ)
  (hF : F.PreservesHomotopy)

/-- A shift-compatible functor of cochain complexes remains shift-compatible after descent to
homotopy categories. -/
noncomputable instance liftCommShift [F.CommShift ℤ] :
    (lift F hF).CommShift ℤ :=
  inferInstanceAs
    ((Quotient.lift (homotopic V (ComplexShape.up ℤ))
      (F ⋙ HomotopyCategory.quotient W (ComplexShape.up ℤ))
      (fun _ _ _ _ h ↦ Quotient.sound (homotopic W (ComplexShape.up ℤ)) (hF h))).CommShift ℤ)

namespace lift

/-- On a quotient object, the shift comparison of a descended functor is induced by the raw
shift comparison, together with the canonical comparison between shifting before and after the
source quotient. -/
@[simp]
theorem commShiftIso_hom_app [F.CommShift ℤ]
    (K : CochainComplex V ℤ) (n : ℤ) :
    ((lift F hF).commShiftIso n).hom.app
        ((HomotopyCategory.quotient V (ComplexShape.up ℤ)).obj K) =
      (lift F hF).map
          (((HomotopyCategory.quotient V (ComplexShape.up ℤ)).commShiftIso n).inv.app K) ≫
        (((F ⋙ HomotopyCategory.quotient W (ComplexShape.up ℤ)).commShiftIso n).hom.app K) := sorry

/-- On a quotient object, the inverse shift comparison of a descended functor is induced by the
inverse raw shift comparison, together with the canonical comparison between shifting before and
after the source quotient. -/
@[simp]
theorem commShiftIso_inv_app [F.CommShift ℤ]
    (K : CochainComplex V ℤ) (n : ℤ) :
    ((lift F hF).commShiftIso n).inv.app
        ((HomotopyCategory.quotient V (ComplexShape.up ℤ)).obj K) =
      (((F ⋙ HomotopyCategory.quotient W (ComplexShape.up ℤ)).commShiftIso n).inv.app K) ≫
        (lift F hF).map
          (((HomotopyCategory.quotient V (ComplexShape.up ℤ)).commShiftIso n).hom.app K) := sorry

end lift

namespace liftFactors

/-- The canonical factorization of a descended functor is compatible with shifts. -/
noncomputable instance homCommShift [F.CommShift ℤ] :
    NatTrans.CommShift (liftFactors F hF).hom ℤ := sorry

end liftFactors

namespace liftIso

variable {G : CochainComplex V ℤ ⥤ CochainComplex W ℤ}
  (hG : G.PreservesHomotopy) (e : F ≅ G)

/-- Descent preserves shift-compatible natural isomorphisms. -/
noncomputable instance homCommShift
    [F.CommShift ℤ] [G.CommShift ℤ] [NatTrans.CommShift e.hom ℤ] :
    NatTrans.CommShift (liftIso hF hG e).hom ℤ := sorry

end liftIso

end Shift



end Homotopy

end CategoryTheory.Functor
