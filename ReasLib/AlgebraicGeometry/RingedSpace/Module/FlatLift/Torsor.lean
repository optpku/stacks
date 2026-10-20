/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatLift
public import ReasLib.AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension.Torsor

/-!
# Ext-valued differences of flat lifts

Flat lift classes map canonically to infinitesimal extension classes. For a strict
morphism of first-order thickenings, a flat reduction and one flat lift make this
comparison bijective. Baer difference then gives the intrinsic principal
homogeneous space description in terms of Ext¹.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Modules
open scoped AlgebraicGeometry

noncomputable section

universe u w

namespace AlgebraicGeometry.RingedSpace.Thickening.Hom.FlatLift

variable {T U : Thickening.{u}} [IsFirstOrderThickening T.hom]
  [IsFirstOrderThickening U.hom]
variable {g : T ⟶ U} {F : T.left.Modules}

/-- Compatible isomorphisms of flat lifts identify their associated infinitesimal
extensions in the extension setoid. -/
theorem toInfinitesimalExtension_respects_isomorphic (hg : IsStrict g)
    [SheafOfModules.IsFlatOver F g.left] {L M : FlatLift g F}
    (h : Isomorphic L M) :
    (InfinitesimalExtension.isoSetoid T.hom F (idealModule T.hom ⊗ F)
      (infMapId T.hom F)).r (toInfinitesimalExtension hg L)
        (toInfinitesimalExtension hg M) := by
  sorry

/-- The canonical map from flat lift classes to identity-comparison extension classes. -/
def toInfinitesimalIsoClass (hg : IsStrict g) [SheafOfModules.IsFlatOver F g.left] :
    IsomorphismClass g F → InfinitesimalExtension.IsoClass T.hom F (idealModule T.hom ⊗ F)
      (infMapId T.hom F) :=
  Quotient.map (toInfinitesimalExtension hg)
    (fun _ _ h => toInfinitesimalExtension_respects_isomorphic hg h)

/-- The comparison on a representative is the class of its associated extension. -/
theorem toInfinitesimalIsoClass_mk (hg : IsStrict g)
    [SheafOfModules.IsFlatOver F g.left] (L : FlatLift g F) :
    toInfinitesimalIsoClass hg (IsomorphismClass.mk L) =
      InfinitesimalExtension.IsoClass.mk (toInfinitesimalExtension hg L) := rfl

/-- For a strict morphism with flat reduction, existence of a flat lift makes every
extension with identity infinitesimal comparison flat over the thickened base. -/
theorem isFlatOver_of_infMapId (hg : IsStrict g) [SheafOfModules.IsFlatOver F g.left]
    (L0 : FlatLift g F)
    (E : InfinitesimalExtension T.hom F (idealModule T.hom ⊗ F) (infMapId T.hom F)) :
    SheafOfModules.IsFlatOver E.module g.right := by
  sorry

/-- For a strict morphism with flat reduction and a flat lift, the associated-extension
map bijects flat lift classes with identity-comparison extension classes. -/
theorem toInfinitesimalIsoClass_bijective (hg : IsStrict g)
    [SheafOfModules.IsFlatOver F g.left] (L0 : FlatLift g F) :
    Function.Bijective (toInfinitesimalIsoClass hg : IsomorphismClass g F → _) := by
  sorry

/-- The Ext¹-valued difference of flat lift classes is the canonical class of their
Baer difference as infinitesimal extensions. -/
def difference (hg : IsStrict g) [SheafOfModules.IsFlatOver F g.left]
    [HasExt.{w} T.left.Modules] (p q : IsomorphismClass g F) :
    CategoryTheory.Abelian.Ext F (idealModule T.hom ⊗ F) 1 :=
  ExtensionClass.toExt.{w} (C := T.left.Modules) (InfinitesimalExtension.vsub (i := T.hom)
    (toInfinitesimalIsoClass hg p) (toInfinitesimalIsoClass hg q))

/-- On flat lift representatives, the Ext¹ difference is the Baer difference of their
associated infinitesimal extension classes followed by the canonical Ext¹ map. -/
theorem difference_mk (hg : IsStrict g) [SheafOfModules.IsFlatOver F g.left]
    [HasExt.{w} T.left.Modules] (L M : FlatLift g F) :
    difference hg (IsomorphismClass.mk L) (IsomorphismClass.mk M) =
      (ExtensionClass.toExt.{w} (InfinitesimalExtension.vsub (i := T.hom)
        (InfinitesimalExtension.IsoClass.mk (i := T.hom) (F := F)
          (K := idealModule T.hom ⊗ F) (c := infMapId T.hom F)
          (toInfinitesimalExtension hg L))
        (InfinitesimalExtension.IsoClass.mk (i := T.hom) (F := F)
          (K := idealModule T.hom ⊗ F) (c := infMapId T.hom F)
          (toInfinitesimalExtension hg M))) :
        CategoryTheory.Abelian.Ext F (idealModule T.hom ⊗ F) 1) := rfl

/-- For a strict morphism of first-order thickenings, the classes of flat lifts of a
module flat over the reduced base form a principal homogeneous space under Ext¹
whenever a flat lift exists: difference from each fixed class is bijective and
satisfies the additive cocycle identity. -/
theorem principalHomogeneous (hg : IsStrict g) [SheafOfModules.IsFlatOver F g.left]
    [HasExt.{w} T.left.Modules] (L0 : FlatLift g F) :
    Nonempty (IsomorphismClass g F) ∧
      (∀ p : IsomorphismClass g F,
        Function.Bijective (fun q : IsomorphismClass g F => difference hg q p)) ∧
      (∀ p q r : IsomorphismClass g F,
        difference hg p r = difference hg p q + difference hg q r) := by
  sorry

end AlgebraicGeometry.RingedSpace.Thickening.Hom.FlatLift
