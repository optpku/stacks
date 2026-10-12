/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.CommSq
public import ReasLib.CategoryTheory.Adjunction.RelativeCupProduct
import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition of relative cup products

The comparison isomorphisms between composite right adjoints do not determine the compatibility
of cup products by functoriality alone.  The counit equation below is the precise coherence needed
to compare the direct and iterated constructions.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe uSource uMiddle uFinal vSource vMiddle vFinal

namespace CategoryTheory

variable {SourceDerived : Type uSource} [Category.{vSource} SourceDerived]
variable {MiddleDerived : Type uMiddle} [Category.{vMiddle} MiddleDerived]
variable {FinalDerived : Type uFinal} [Category.{vFinal} FinalDerived]

variable {leftDerivedPullback_f : MiddleDerived ⥤ SourceDerived}
  {rightDerivedPushforward_f : SourceDerived ⥤ MiddleDerived}
  (pullPushAdj_f : leftDerivedPullback_f ⊣ rightDerivedPushforward_f)
  {leftDerivedPullback_g : FinalDerived ⥤ MiddleDerived}
  {rightDerivedPushforward_g : MiddleDerived ⥤ FinalDerived}
  (pullPushAdj_g : leftDerivedPullback_g ⊣ rightDerivedPushforward_g)
  {leftDerivedPullback_comp : FinalDerived ⥤ SourceDerived}
  {rightDerivedPushforward_comp : SourceDerived ⥤ FinalDerived}
  (pullPushAdj_comp : leftDerivedPullback_comp ⊣ rightDerivedPushforward_comp)
  (reindexCompIso : leftDerivedPullback_g ⋙ leftDerivedPullback_f ≅ leftDerivedPullback_comp)
  (pushforwardCompIso :
    rightDerivedPushforward_f ⋙ rightDerivedPushforward_g ≅ rightDerivedPushforward_comp)
  (pushforwardCompIso_hom_counit :
    Functor.whiskerRight pushforwardCompIso.hom leftDerivedPullback_comp ≫
        pullPushAdj_comp.counit =
      ((pullPushAdj_g.comp pullPushAdj_f).ofNatIsoLeft reindexCompIso).counit)
  (tensorSource : SourceDerived ⥤ SourceDerived ⥤ SourceDerived)
  (tensorMiddle : MiddleDerived ⥤ MiddleDerived ⥤ MiddleDerived)
  (tensorFinal : FinalDerived ⥤ FinalDerived ⥤ FinalDerived)
  (pullbackTensorIso_f :
    ∀ (K L : MiddleDerived),
      leftDerivedPullback_f.obj ((tensorMiddle.obj L).obj K) ≅
        ((tensorSource.obj (leftDerivedPullback_f.obj L)).obj
          (leftDerivedPullback_f.obj K)))
  (pullbackTensorIso_g :
    ∀ (K L : FinalDerived),
      leftDerivedPullback_g.obj ((tensorFinal.obj L).obj K) ≅
        ((tensorMiddle.obj (leftDerivedPullback_g.obj L)).obj
          (leftDerivedPullback_g.obj K)))
  (pullbackTensorIso_comp :
    ∀ (K L : FinalDerived),
      leftDerivedPullback_comp.obj ((tensorFinal.obj L).obj K) ≅
        ((tensorSource.obj (leftDerivedPullback_comp.obj L)).obj
          (leftDerivedPullback_comp.obj K)))

namespace RelativeDerivedCupProductComp

/-- The source-side comparison induced by the composite right-adjoint isomorphism. -/
abbrev source
    (pushforwardCompIso :
      rightDerivedPushforward_f ⋙ rightDerivedPushforward_g ≅ rightDerivedPushforward_comp)
    (tensorFinal : FinalDerived ⥤ FinalDerived ⥤ FinalDerived) (K L : SourceDerived) :
    (tensorFinal.obj (rightDerivedPushforward_comp.obj L)).obj
        (rightDerivedPushforward_comp.obj K) ⟶
      (tensorFinal.obj
          (rightDerivedPushforward_g.obj (rightDerivedPushforward_f.obj L))).obj
        (rightDerivedPushforward_g.obj (rightDerivedPushforward_f.obj K)) :=
  ((tensorFinal.map (pushforwardCompIso.inv.app L)).app
      (rightDerivedPushforward_comp.obj K)) ≫
    (tensorFinal.obj
      (rightDerivedPushforward_g.obj (rightDerivedPushforward_f.obj L))).map
      (pushforwardCompIso.inv.app K)

/-- The target-side comparison induced by the composite right-adjoint isomorphism. -/
abbrev target
    (pushforwardCompIso :
      rightDerivedPushforward_f ⋙ rightDerivedPushforward_g ≅ rightDerivedPushforward_comp)
    (tensorSource : SourceDerived ⥤ SourceDerived ⥤ SourceDerived) (K L : SourceDerived) :
    rightDerivedPushforward_comp.obj ((tensorSource.obj L).obj K) ⟶
      rightDerivedPushforward_g.obj
        (rightDerivedPushforward_f.obj ((tensorSource.obj L).obj K)) :=
  pushforwardCompIso.inv.app ((tensorSource.obj L).obj K)

/-- The iterated cup-product map through the two right adjoints. -/
abbrev iterated
    (pullPushAdj_f : leftDerivedPullback_f ⊣ rightDerivedPushforward_f)
    (pullPushAdj_g : leftDerivedPullback_g ⊣ rightDerivedPushforward_g)
    (tensorSource : SourceDerived ⥤ SourceDerived ⥤ SourceDerived)
    (tensorMiddle : MiddleDerived ⥤ MiddleDerived ⥤ MiddleDerived)
    (tensorFinal : FinalDerived ⥤ FinalDerived ⥤ FinalDerived)
    (pullbackTensorIso_f :
      ∀ (K L : MiddleDerived),
        leftDerivedPullback_f.obj ((tensorMiddle.obj L).obj K) ≅
          ((tensorSource.obj (leftDerivedPullback_f.obj L)).obj
            (leftDerivedPullback_f.obj K)))
    (pullbackTensorIso_g :
      ∀ (K L : FinalDerived),
        leftDerivedPullback_g.obj ((tensorFinal.obj L).obj K) ≅
          ((tensorMiddle.obj (leftDerivedPullback_g.obj L)).obj
            (leftDerivedPullback_g.obj K)))
    (K L : SourceDerived) :
    (tensorFinal.obj
        (rightDerivedPushforward_g.obj (rightDerivedPushforward_f.obj L))).obj
      (rightDerivedPushforward_g.obj (rightDerivedPushforward_f.obj K)) ⟶
      rightDerivedPushforward_g.obj
        (rightDerivedPushforward_f.obj ((tensorSource.obj L).obj K)) :=
  pullPushAdj_g.rightAdjointTensorMapOf tensorFinal tensorMiddle
      (fun A B ↦ (pullbackTensorIso_g B A).hom)
      (rightDerivedPushforward_f.obj L) (rightDerivedPushforward_f.obj K) ≫
    rightDerivedPushforward_g.map
      (pullPushAdj_f.rightAdjointTensorMapOf tensorMiddle tensorSource
        (fun A B ↦ (pullbackTensorIso_f B A).hom) L K)

end RelativeDerivedCupProductComp

include pushforwardCompIso_hom_counit in
/-- The relative cup product is compatible with composition of right adjoints. -/
@[stacks 0FPN "composition of relative derived cup products"]
theorem relativeDerivedCupProduct_comp_commSq
    (K L : SourceDerived) :
    CommSq
      (pullPushAdj_comp.rightAdjointTensorMapOf tensorFinal tensorSource
        (fun A B ↦ (pullbackTensorIso_comp B A).hom) L K)
      (RelativeDerivedCupProductComp.source
        pushforwardCompIso tensorFinal K L)
      (RelativeDerivedCupProductComp.target
        pushforwardCompIso tensorSource K L)
      (RelativeDerivedCupProductComp.iterated
        pullPushAdj_f pullPushAdj_g tensorSource tensorMiddle tensorFinal
        pullbackTensorIso_f pullbackTensorIso_g K L) := sorry

include pushforwardCompIso_hom_counit in
/-- Equality form of composition compatibility for relative cup products. -/
@[stacks 0FPN "composition equality for relative derived cup products"]
theorem relativeDerivedCupProduct_comp_eq_iterated
    (K L : SourceDerived) :
    pullPushAdj_comp.rightAdjointTensorMapOf tensorFinal tensorSource
        (fun A B ↦ (pullbackTensorIso_comp B A).hom) L K =
      (RelativeDerivedCupProductComp.source
        pushforwardCompIso tensorFinal K L) ≫
        (RelativeDerivedCupProductComp.iterated
          pullPushAdj_f pullPushAdj_g tensorSource tensorMiddle tensorFinal
          pullbackTensorIso_f pullbackTensorIso_g K L) ≫
        pushforwardCompIso.hom.app ((tensorSource.obj L).obj K) := sorry

end CategoryTheory
