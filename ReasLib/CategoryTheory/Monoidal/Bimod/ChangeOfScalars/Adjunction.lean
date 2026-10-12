/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Monoidal.Bimod.ChangeOfScalars
import Mathlib.Tactic.CrossRefAttribute

/-!
# Adjunctions for change of scalars of module objects

Extension of scalars for right modules is left adjoint to restriction of scalars.  More
generally, a monoidal adjunction transports this construction across the ambient categories:
a morphism `F(A) ⟶ B` determines base change from `A`-modules to `B`-modules, whose right
adjoint is monoidal transport by `G` followed by restriction along the adjoint mate
`A ⟶ G(B)`.
-/

@[expose] public section

open CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

noncomputable section

universe uC vC uD vD

namespace CategoryTheory.Bimod

variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
variable [HasCoequalizers C]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)]
variable {A B : Mon C}

/-- Transpose a morphism out of an extended right module to a morphism into the restricted
module.  On carriers this inserts the unit of the target monoid before the balanced quotient. -/
noncomputable def extendRestrictRightHomForward (f : A ⟶ B)
    (M : RightModule A) (N : RightModule B)
    (g : (extendRight f).obj M ⟶ N) :
    M ⟶ (restrictRight (Mon.trivial C) f).obj N where
  hom := (ρ_ M.X).inv ≫ (M.X ◁ η[B.X]) ≫ coequalizer.π _ _ ≫ g.hom
  left_act_hom := sorry
  right_act_hom := sorry

/-- Transpose a morphism into a restricted right module to a morphism out of extension of
scalars.  The carrier map is induced by the balanced coequalizer. -/
noncomputable def extendRestrictRightHomBackward (f : A ⟶ B)
    (M : RightModule A) (N : RightModule B)
    (g : M ⟶ (restrictRight (Mon.trivial C) f).obj N) :
    (extendRight f).obj M ⟶ N where
  hom := coequalizer.desc ((g.hom ▷ B.X) ≫ N.actRight) sorry
  left_act_hom := sorry
  right_act_hom := sorry

/-- The canonical extension-restriction Hom equivalence for right modules over monoid
objects. -/
@[stacks 0FSA "right module extension-restriction Hom equivalence"]
noncomputable def extendRestrictRightHomEquiv (f : A ⟶ B)
    (M : RightModule A) (N : RightModule B) :
    ((extendRight f).obj M ⟶ N) ≃
      (M ⟶ (restrictRight (Mon.trivial C) f).obj N) where
  toFun := extendRestrictRightHomForward f M N
  invFun := extendRestrictRightHomBackward f M N
  left_inv := sorry
  right_inv := sorry

/-- The natural Hom equivalences defining extension-restriction adjunction for right
modules. -/
noncomputable def extendRestrictRightCoreHomEquiv (f : A ⟶ B) :
    Adjunction.CoreHomEquiv (extendRight f) (restrictRight (Mon.trivial C) f) where
  homEquiv := extendRestrictRightHomEquiv f
  homEquiv_naturality_left_symm := sorry
  homEquiv_naturality_right := sorry

/-- Extension of scalars is left adjoint to restriction of scalars for right modules over
monoid objects. -/
@[stacks 0FSA "right module extension-restriction adjunction"]
noncomputable def extendRestrictRightAdjunction (f : A ⟶ B) :
    extendRight f ⊣ restrictRight (Mon.trivial C) f :=
  Adjunction.mkOfHomEquiv (extendRestrictRightCoreHomEquiv f)

/-- The Hom equivalence of the extension-restriction adjunction is the explicit balanced
tensor transpose. -/
theorem extendRestrictRightAdjunction_homEquiv (f : A ⟶ B)
    (M : RightModule A) (N : RightModule B) :
    (extendRestrictRightAdjunction f).homEquiv M N =
      extendRestrictRightHomEquiv f M N := sorry

end CategoryTheory.Bimod

namespace CategoryTheory.Adjunction

variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
variable {D : Type uD} [Category.{vD} D] [MonoidalCategory D]
variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
variable [F.Monoidal] [G.LaxMonoidal] [adj.IsMonoidal]

/-- The right adjoint to monoidal transport of right `A`-modules.  It applies `G` and then
restricts scalars along the unit `A ⟶ G(F(A))` of the induced adjunction on monoids. -/
@[stacks 0FRU "right adjoint to monoidal transport of modules"]
noncomputable def mapRightModulePushforward (A : Mon C) :
    Bimod.RightModule (F.mapMon.obj A) ⥤ Bimod.RightModule A :=
  G.mapRightModule (F.mapMon.obj A) ⋙
    Bimod.restrictRight (Mon.trivial C) (adj.mapMon.unit.app A)

/-- Transpose a morphism of transported right modules across the ambient monoidal
adjunction. -/
noncomputable def mapRightModuleHomForward (A : Mon C)
    (M : Bimod.RightModule A) (N : Bimod.RightModule (F.mapMon.obj A))
    (g : (F.mapRightModule A).obj M ⟶ N) :
    M ⟶ (adj.mapRightModulePushforward A).obj N where
  hom := adj.homEquiv M.X N.X g.hom
  left_act_hom := sorry
  right_act_hom := sorry

/-- Transpose a morphism of transported right modules backwards across the ambient monoidal
adjunction. -/
noncomputable def mapRightModuleHomBackward (A : Mon C)
    (M : Bimod.RightModule A) (N : Bimod.RightModule (F.mapMon.obj A))
    (g : M ⟶ (adj.mapRightModulePushforward A).obj N) :
    (F.mapRightModule A).obj M ⟶ N where
  hom := (adj.homEquiv M.X N.X).symm g.hom
  left_act_hom := sorry
  right_act_hom := sorry

/-- The Hom equivalence lifting a monoidal adjunction to right modules over a fixed source
monoid. -/
@[stacks 0FRU "monoidal transport of right modules Hom equivalence"]
noncomputable def mapRightModuleHomEquiv (A : Mon C)
    (M : Bimod.RightModule A) (N : Bimod.RightModule (F.mapMon.obj A)) :
    ((F.mapRightModule A).obj M ⟶ N) ≃
      (M ⟶ (adj.mapRightModulePushforward A).obj N) where
  toFun := adj.mapRightModuleHomForward A M N
  invFun := adj.mapRightModuleHomBackward A M N
  left_inv := sorry
  right_inv := sorry

/-- The natural Hom equivalences lifting a monoidal adjunction to right modules over a fixed
source monoid. -/
noncomputable def mapRightModuleCoreHomEquiv (A : Mon C) :
    Adjunction.CoreHomEquiv (F.mapRightModule A) (adj.mapRightModulePushforward A) where
  homEquiv := adj.mapRightModuleHomEquiv A
  homEquiv_naturality_left_symm := sorry
  homEquiv_naturality_right := sorry

/-- Monoidal transport of right modules is left adjoint to transport by the right adjoint
followed by restriction along the monoid-level unit. -/
@[stacks 0FRU "monoidal transport of right modules adjunction"]
noncomputable def mapRightModuleAdjunction (A : Mon C) :
    F.mapRightModule A ⊣ adj.mapRightModulePushforward A :=
  Adjunction.mkOfHomEquiv (adj.mapRightModuleCoreHomEquiv A)

/-- The adjoint mate of a target monoid morphism `F(A) ⟶ B`. -/
@[stacks 0FRU "adjoint mate of the coefficient morphism"]
noncomputable def rightModuleMate {A : Mon C} {B : Mon D}
    (f : F.mapMon.obj A ⟶ B) : A ⟶ G.mapMon.obj B :=
  adj.mapMon.homEquiv A B f

/-- The direct right adjoint to right-module base change along `f : F(A) ⟶ B`: transport
by `G`, then restrict scalars along the mate `A ⟶ G(B)`. -/
@[stacks 0FRU "right module pushforward along a coefficient morphism"]
noncomputable def baseChangeRightPushforward {A : Mon C} {B : Mon D}
    (f : F.mapMon.obj A ⟶ B) :
    Bimod.RightModule B ⥤ Bimod.RightModule A :=
  G.mapRightModule B ⋙
    Bimod.restrictRight (Mon.trivial C) (adj.rightModuleMate f)

/-- The compositional right adjoint to base change, before identifying its two successive
scalar restrictions with restriction along the mate. -/
noncomputable def baseChangeRightCompPushforward {A : Mon C} {B : Mon D}
    (f : F.mapMon.obj A ⟶ B) :
    Bimod.RightModule B ⥤ Bimod.RightModule A :=
  Bimod.restrictRight (Mon.trivial D) f ⋙ adj.mapRightModulePushforward A

/-- Successive restriction after monoidal transport is canonically isomorphic to direct
restriction along the adjoint mate of the coefficient morphism. -/
@[stacks 0FRU "mate comparison for right module pushforward"]
noncomputable def baseChangeRightPushforwardIso {A : Mon C} {B : Mon D}
    (f : F.mapMon.obj A ⟶ B) :
    adj.baseChangeRightCompPushforward f ≅ adj.baseChangeRightPushforward f :=
  NatIso.ofComponents
    (fun N ↦ Bimod.isoOfIso (Iso.refl (G.obj N.X)) sorry sorry)
    (fun _ ↦ sorry)

section

variable [HasCoequalizers D]
variable [∀ X : D, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)]
variable [∀ X : D, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)]

/-- Right-module base change along `f : F(A) ⟶ B` is left adjoint to transport by `G`
followed by restriction along its mate `A ⟶ G(B)`. -/
@[stacks 0FRU "right module base-change adjunction"]
noncomputable def baseChangeRightAdjunction {A : Mon C} {B : Mon D}
    (f : F.mapMon.obj A ⟶ B) :
    F.baseChangeRight A f ⊣ adj.baseChangeRightPushforward f :=
  ((adj.mapRightModuleAdjunction A).comp
    (Bimod.extendRestrictRightAdjunction f)).ofNatIsoRight
      (adj.baseChangeRightPushforwardIso f)

/-- The reusable Hom equivalence for right-module base change along a morphism of transported
monoids. -/
@[stacks 0FRU "right module base-change Hom equivalence"]
noncomputable def baseChangeRightHomEquiv {A : Mon C} {B : Mon D}
    (f : F.mapMon.obj A ⟶ B) (M : Bimod.RightModule A)
    (N : Bimod.RightModule B) :
    ((F.baseChangeRight A f).obj M ⟶ N) ≃
      (M ⟶ (adj.baseChangeRightPushforward f).obj N) :=
  (adj.baseChangeRightAdjunction f).homEquiv M N

end

end CategoryTheory.Adjunction

end
