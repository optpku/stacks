/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.NaiveCotangent.Transitivity
public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent.Functoriality
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Base change for naive cotangent complexes of schemes

A commutative square of schemes induces a canonical morphism from the pullback of the naive
cotangent complex of its right edge to the naive cotangent complex of its left edge.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ComplexShape TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom
namespace NaiveCotangent.BaseChange

variable {X X' Y Y' : _root_.AlgebraicGeometry.Scheme.{u}}
variable {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The coefficient-sheaf morphism underlying naive-cotangent base change for a commutative
square of schemes. -/
noncomputable def coefficientMap (sq : CommSq g' f' f g) :
    RingedSpace.NaiveCotangent.Tower.source g'.toShHom f.toShHom ⟶
      RingedSpace.NaiveCotangent.Tower.middle f'.toShHom :=
  let shSq :=
    (sq.map (_root_.AlgebraicGeometry.Scheme.forgetToLocallyRingedSpace ⋙
      LocallyRingedSpace.forgetToSheafedSpace) :
        CommSq g'.toShHom f'.toShHom f.toShHom g.toShHom)
  (RingedSpace.Hom.StructureSheaf.compIso g'.toShHom f.toShHom).hom ≫
    (TopCat.Sheaf.pullbackCongr (A := CommRingCat.{u})
      (congrArg (fun k : X'.toSheafedSpace ⟶ Y.toSheafedSpace ↦ k.hom.base)
        shSq.w)).hom.app Y.sheaf ≫
    (RingedSpace.Hom.StructureSheaf.compIso f'.toShHom g.toShHom).inv ≫
    (TopCat.Sheaf.pullback CommRingCat.{u} f'.base).map
      (RingedSpace.Hom.inverseImageStructureSheafHomComm g.toShHom)

/-- The coefficient map is compatible with the two structure-sheaf maps in the square. -/
theorem coefficientSquare (sq : CommSq g' f' f g) :
    CommSq (coefficientMap sq)
      (RingedSpace.NaiveCotangent.Tower.first g'.toShHom f.toShHom)
      (RingedSpace.Hom.inverseImageStructureSheafHomComm f'.toShHom)
      (RingedSpace.NaiveCotangent.Tower.second g'.toShHom) := by
  refine ⟨?_⟩
  change coefficientMap sq ≫
      RingedSpace.Hom.inverseImageStructureSheafHomComm f'.toShHom =
    RingedSpace.Hom.StructureSheaf.compositeMap g'.toShHom f.toShHom
  rw [RingedSpace.Hom.StructureSheaf.compositeMap_eq]
  rw [coefficientMap]
  have hfg := RingedSpace.Hom.StructureSheaf.compositeMap_eq
    f'.toShHom g.toShHom
  change
    (TopCat.Sheaf.pullback CommRingCat.{u} f'.base).map
          (RingedSpace.Hom.inverseImageStructureSheafHomComm g.toShHom) ≫
        RingedSpace.Hom.inverseImageStructureSheafHomComm f'.toShHom =
      (RingedSpace.Hom.StructureSheaf.compIso f'.toShHom g.toShHom).hom ≫
        RingedSpace.Hom.inverseImageStructureSheafHomComm
          (f'.toShHom ≫ g.toShHom) at hfg
  simp only [Category.assoc]
  rw [cancel_epi]
  erw [hfg]
  erw [Iso.inv_hom_id_assoc]
  let shSq :=
    (sq.map (_root_.AlgebraicGeometry.Scheme.forgetToLocallyRingedSpace ⋙
      LocallyRingedSpace.forgetToSheafedSpace) :
        CommSq g'.toShHom f'.toShHom f.toShHom g.toShHom)
  change
    (TopCat.Sheaf.pullbackCongr (A := CommRingCat.{u})
          (congrArg (fun k : X'.toSheafedSpace ⟶ Y.toSheafedSpace ↦ k.hom.base)
            shSq.w)).hom.app Y.sheaf ≫
        RingedSpace.Hom.inverseImageStructureSheafHomComm
          (f'.toShHom ≫ g.toShHom) =
      RingedSpace.Hom.inverseImageStructureSheafHomComm
        (g'.toShHom ≫ f.toShHom)
  have pullbackCongr_comp_inverseImageStructureSheafHomComm
      {a b : X'.toSheafedSpace ⟶ Y.toSheafedSpace} (h : a = b) :
      (TopCat.Sheaf.pullbackCongr (A := CommRingCat.{u})
            (congrArg (fun k : X'.toSheafedSpace ⟶ Y.toSheafedSpace ↦ k.hom.base)
              h)).hom.app Y.sheaf ≫
          RingedSpace.Hom.inverseImageStructureSheafHomComm b =
        RingedSpace.Hom.inverseImageStructureSheafHomComm a := by
    subst b
    rfl
  exact pullbackCongr_comp_inverseImageStructureSheafHomComm shSq.w

/-- The canonical map from the pullback of `NL(f)` to `NL(f')` associated to a commutative
square of schemes. -/
noncomputable def map (sq : CommSq g' f' f g) :
    (((_root_.AlgebraicGeometry.Scheme.Modules.pullback g').mapHomologicalComplex (up ℤ)).obj
        (RingedSpace.naiveCotangent f.toShHom)) ⟶
      RingedSpace.naiveCotangent f'.toShHom :=
by
  let e : RingedSpace.NaiveCotangent.Pullback.chosenComplex g'.toShHom f.toShHom ≅
      RingedSpace.NaiveCotangent.pullbackComplex g'.toShHom f.toShHom :=
    RingedSpace.NaiveCotangent.Pullback.chosenComplexIso g'.toShHom f.toShHom
  let m : RingedSpace.NaiveCotangent.pullbackComplex g'.toShHom f.toShHom ⟶
      RingedSpace.naiveCotangent f'.toShHom :=
    SheafOfModules.RingedSite.NaiveCotangent.map.{u, u, u}
      (C := Opens X') (J := Opens.grothendieckTopology X')
      (α := RingedSpace.NaiveCotangent.Tower.first g'.toShHom f.toShHom)
      (ρ := coefficientMap sq)
      (β := RingedSpace.Hom.inverseImageStructureSheafHomComm f'.toShHom)
      (φ := RingedSpace.NaiveCotangent.Tower.second g'.toShHom)
      (coefficientSquare sq)
  exact e.hom ≫ m

/-- The base-change map is the chosen-pullback normalization followed by the canonical map
associated to its coefficient square. -/
theorem map_eq (sq : CommSq g' f' f g) :
    map sq =
      (RingedSpace.NaiveCotangent.Pullback.chosenComplexIso
          g'.toShHom f.toShHom).hom ≫
        SheafOfModules.RingedSite.NaiveCotangent.map.{u, u, u}
          (C := Opens X') (J := Opens.grothendieckTopology X')
          (α := RingedSpace.NaiveCotangent.Tower.first g'.toShHom f.toShHom)
          (ρ := coefficientMap sq)
          (β := RingedSpace.Hom.inverseImageStructureSheafHomComm f'.toShHom)
          (φ := RingedSpace.NaiveCotangent.Tower.second g'.toShHom)
          (coefficientSquare sq) := rfl

end NaiveCotangent.BaseChange
end AlgebraicGeometry.Scheme.Hom
