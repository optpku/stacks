/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.FunctorCategory.Pointwise.Coproduct
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Definition

@[expose] public section

open CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v v' u u'

namespace CategoryTheory.HomotopyColimit.Functorial

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D] [Limits.HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- A sequential diagram of functors presents a target functor as its homotopy colimit when
it has a functor-category coproduct and natural telescope maps whose evaluations are
distinguished telescope triangles. -/
def IsOf (S : ℕ ⥤ (C ⥤ D)) (F : C ⥤ D) : Prop :=
  ∃ P : ColimitCocone (Discrete.functor S.obj),
    ∃ pointwise : ∀ c : C,
      IsColimit (((evaluation C D).obj c).mapCocone P.cocone),
    ∃ toCocone : P.cocone.pt ⟶ F,
      ∃ connecting : F ⟶ P.cocone.pt ⋙ shiftFunctor D (1 : ℤ),
        ∀ c : C,
          let Pc : ColimitCocone
              (Discrete.functor (S ⋙ (evaluation C D).obj c).obj) :=
            ⟨(Cocone.precompose
                (Discrete.compNatIsoDiscrete S.obj ((evaluation C D).obj c)).inv).obj
                  (((evaluation C D).obj c).mapCocone P.cocone),
              (IsColimit.precomposeInvEquiv
                (Discrete.compNatIsoDiscrete S.obj ((evaluation C D).obj c)) _).symm
                  (pointwise c)⟩
          Triangle.mk (Limits.Sequential.CoproductCocone.telescopeMap
              (S ⋙ (evaluation C D).obj c) Pc)
            (toCocone.app c) (connecting.app c) ∈ distTriang D

/-- The explicit coproduct, natural telescope maps, and evaluated distinguished triangles
that characterize a functorial sequential homotopy-colimit presentation. -/
theorem isOf_iff (S : ℕ ⥤ (C ⥤ D)) (F : C ⥤ D) :
    IsOf S F ↔
      ∃ P : ColimitCocone (Discrete.functor S.obj),
        ∃ pointwise : ∀ c : C,
          IsColimit (((evaluation C D).obj c).mapCocone P.cocone),
        ∃ toCocone : P.cocone.pt ⟶ F,
          ∃ connecting : F ⟶ P.cocone.pt ⋙ shiftFunctor D (1 : ℤ),
            ∀ c : C,
              let Pc : ColimitCocone
                  (Discrete.functor (S ⋙ (evaluation C D).obj c).obj) :=
                ⟨(Cocone.precompose
                    (Discrete.compNatIsoDiscrete S.obj ((evaluation C D).obj c)).inv).obj
                      (((evaluation C D).obj c).mapCocone P.cocone),
                  (IsColimit.precomposeInvEquiv
                    (Discrete.compNatIsoDiscrete S.obj ((evaluation C D).obj c)) _).symm
                      (pointwise c)⟩
              Triangle.mk (Limits.Sequential.CoproductCocone.telescopeMap
                  (S ⋙ (evaluation C D).obj c) Pc)
                (toCocone.app c) (connecting.app c) ∈ distTriang D := sorry

namespace IsOf

/-- Evaluating a functorial presentation gives the corresponding objectwise sequential
homotopy-colimit presentation. -/
theorem eval {S : ℕ ⥤ (C ⥤ D)} {F : C ⥤ D} (h : IsOf S F) (c : C) :
    HomotopyColimit.IsOf (S ⋙ (evaluation C D).obj c) (F.obj c) := sorry

/-- A functorial homotopy-colimit presentation transports across an isomorphism of target
functors. -/
theorem ofIso {S : ℕ ⥤ (C ⥤ D)} {F G : C ⥤ D} (h : IsOf S F) (e : F ≅ G) :
    IsOf S G := sorry

end IsOf

end CategoryTheory.HomotopyColimit.Functorial
