/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.LocalSectionMul
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Definition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open ComplexShape

noncomputable section

universe u v w z

namespace RingedSite.Hom.ModuleDerived

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {O : Sheaf J CommRingCat.{w}} [UnivLE.{max u v, z}]

/-- Canonical derived-category structure on modules over a commutative ring sheaf. -/
noncomputable instance instModuleCatHasDerivedCategory :
    HasDerivedCategory.{max (max (max u v) w) (z + 1)}
      (ModuleCat.{z} (RingedSite.ofCommRingSheaf J O)) :=
  RingedSite.Hom.moduleCat_hasDerivedCategory (RingedSite.ofCommRingSheaf J O)

/-- Multiplication by a local section commutes with the differential after restriction to the
slice site. -/
theorem localSectionActionComplex_comm
    (K : ModuleDerived.{z} (RingedSite.ofCommRingSheaf J O))
    (U : C) (f : O.obj.obj (op U)) (i j : ℤ) (hij : (up ℤ).Rel i j) :
    SheafOfModules.sectionActionHom O
        ((DerivedCategory.Q.objPreimage K).X i) U f ≫
      ((localizedRestrictionComplex.{z}
        (RingedSite.ofCommRingSheaf J O) U).obj
          (DerivedCategory.Q.objPreimage K)).d i j =
    ((localizedRestrictionComplex.{z}
        (RingedSite.ofCommRingSheaf J O) U).obj
          (DerivedCategory.Q.objPreimage K)).d i j ≫
      SheafOfModules.sectionActionHom O
        ((DerivedCategory.Q.objPreimage K).X j) U f := sorry

/-- Multiplication by `f` on the chosen restricted complex representative of `K`. -/
noncomputable def localSectionActionComplex
    (K : ModuleDerived.{z} (RingedSite.ofCommRingSheaf J O))
    (U : C) (f : O.obj.obj (op U)) :
    End ((localizedRestrictionComplex.{z}
      (RingedSite.ofCommRingSheaf J O) U).obj
        (DerivedCategory.Q.objPreimage K)) where
  f i := SheafOfModules.sectionActionHom O
    ((DerivedCategory.Q.objPreimage K).X i) U f
  comm' i j hij := localSectionActionComplex_comm K U f i j hij

/-- The degreewise component of multiplication by a local section is the canonical
module-sheaf section action. -/
theorem localSectionActionComplex_f
    (K : ModuleDerived.{z} (RingedSite.ofCommRingSheaf J O))
    (U : C) (f : O.obj.obj (op U)) (i : ℤ) :
    (localSectionActionComplex K U f).f i =
      SheafOfModules.sectionActionHom O
        ((DerivedCategory.Q.objPreimage K).X i) U f := sorry

/-- Multiplication by a local section is natural in the module sheaf being restricted. -/
theorem localSectionAction_naturality
    (U : C) (f : O.obj.obj (op U))
    {M N : ModuleCat.{z} (RingedSite.ofCommRingSheaf J O)} (g : M ⟶ N) :
    (localizedRestriction.{z} (RingedSite.ofCommRingSheaf J O) U).map g ≫
        SheafOfModules.sectionActionHom O N U f =
      SheafOfModules.sectionActionHom O M U f ≫
        (localizedRestriction.{z} (RingedSite.ofCommRingSheaf J O) U).map g := sorry

/-- Multiplication by `f` as a natural endomorphism of restriction to the localized site. -/
noncomputable def localSectionActionNatTrans
    (U : C) (f : O.obj.obj (op U)) :
    localizedRestriction.{z} (RingedSite.ofCommRingSheaf J O) U ⟶
      localizedRestriction.{z} (RingedSite.ofCommRingSheaf J O) U where
  app M := SheafOfModules.sectionActionHom O M U f
  naturality _ _ g := localSectionAction_naturality U f g

/-- The component of the local-section natural transformation is the sheaf-level section
action. -/
theorem localSectionActionNatTrans_app
    (U : C) (f : O.obj.obj (op U))
    (M : ModuleCat.{z} (RingedSite.ofCommRingSheaf J O)) :
    (localSectionActionNatTrans U f).app M =
      SheafOfModules.sectionActionHom O M U f := sorry

/-- Restriction to `U`, bundled with its canonical exactness properties. -/
public noncomputable abbrev localizedRestrictionExact (U : C) :
    ExactFunctor (ModuleCat.{z} (RingedSite.ofCommRingSheaf J O))
      (ModuleCat.{z} ((RingedSite.ofCommRingSheaf J O).localization U)) :=
  ExactFunctor.of (localizedRestriction.{z} (RingedSite.ofCommRingSheaf J O) U)

/-- The underlying functor of exact localized restriction is localized restriction. -/
theorem localizedRestrictionExact_obj (U : C) :
    (localizedRestrictionExact (O := O) U).obj =
      localizedRestriction.{z} (RingedSite.ofCommRingSheaf J O) U := sorry

/-- Multiplication by a local section as a morphism of exact restriction functors. -/
public noncomputable def localSectionActionExact
    (U : C) (f : O.obj.obj (op U)) :
    localizedRestrictionExact (O := O) U ⟶ localizedRestrictionExact (O := O) U :=
  ObjectProperty.homMk (P := exactFunctor _ _) (localSectionActionNatTrans U f)

/-- The underlying natural transformation of the exact local action is the local action. -/
theorem localSectionActionExact_hom
    (U : C) (f : O.obj.obj (op U)) :
    (localSectionActionExact (O := O) U f).hom = localSectionActionNatTrans U f := sorry

/-- Multiplication by `f` on the derived restriction of `K`. -/
noncomputable def localSectionAction
    (K : ModuleDerived.{z} (RingedSite.ofCommRingSheaf J O))
    (U : C) (f : O.obj.obj (op U)) :
    End ((localizedRestrictionDerived.{z}
      (RingedSite.ofCommRingSheaf J O) U).obj K) :=
  (@ExactFunctor.MapDerivedCategory.map
    _ _ _ (RingedSite.Hom.moduleCat_hasDerivedCategory
      (RingedSite.ofCommRingSheaf J O))
    _ _ _ (RingedSite.Hom.localizedModuleCatHasDerivedCategory
      (X := RingedSite.ofCommRingSheaf J O) U)
    _ _ (localSectionActionExact (O := O) U f)).app K

/-- The derived local section action is induced by the exact local section action. -/
theorem localSectionAction_eq
    (K : ModuleDerived.{z} (RingedSite.ofCommRingSheaf J O))
    (U : C) (f : O.obj.obj (op U)) :
    localSectionAction K U f =
      (@ExactFunctor.MapDerivedCategory.map
        _ _ _ (RingedSite.Hom.moduleCat_hasDerivedCategory
          (RingedSite.ofCommRingSheaf J O))
        _ _ _ (RingedSite.Hom.localizedModuleCatHasDerivedCategory
          (X := RingedSite.ofCommRingSheaf J O) U)
        _ _ (localSectionActionExact (O := O) U f)).app K := sorry

/-- The inverse system defining `T(K|_U, f)`: every stage is the restricted derived object and
every transition map is multiplication by `f`. -/
abbrev localizationAwayTower
    (K : ModuleDerived.{z} (RingedSite.ofCommRingSheaf J O))
    (U : C) (f : O.obj.obj (op U)) :
    SequentialInverseSystem
      (ModuleDerived.{z} ((RingedSite.ofCommRingSheaf J O).localization U)) :=
  Functor.ofOpSequence (X := fun _ ↦
    (localizedRestrictionDerived.{z}
      (RingedSite.ofCommRingSheaf J O) U).obj K)
    (fun _ ↦ localSectionAction K U f)

/-- Every object of the localization-away tower is the derived restriction of `K`. -/
theorem localizationAwayTower_obj
    (K : ModuleDerived.{z} (RingedSite.ofCommRingSheaf J O))
    (U : C) (f : O.obj.obj (op U)) (n : ℕᵒᵖ) :
    (localizationAwayTower K U f).obj n =
      (localizedRestrictionDerived.{z}
        (RingedSite.ofCommRingSheaf J O) U).obj K := sorry

/-- Every successor transition in the localization-away tower is multiplication by `f`. -/
theorem localizationAwayTower_map_succ
    (K : ModuleDerived.{z} (RingedSite.ofCommRingSheaf J O))
    (U : C) (f : O.obj.obj (op U)) (n : ℕ) :
    (localizationAwayTower K U f).map
      (homOfLE (Nat.le_add_right n 1)).op = localSectionAction K U f := sorry

end RingedSite.Hom.ModuleDerived
