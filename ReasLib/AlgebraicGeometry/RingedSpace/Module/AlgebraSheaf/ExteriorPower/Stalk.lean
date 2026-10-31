/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.Stalk
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.ExteriorPower
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk.Skyscraper

/-!
# The inverse homogeneous exterior-power stalk comparison

The inverse in degree `n` is induced by the alternating map which represents finitely many
module germs on a common neighborhood and then takes the germ of their local exterior product.
Representatives come from mathlib's proved `TopCat.Presheaf.exists_germ_eq`; no inverse is
selected from a bijectivity or `IsIso` assertion. The empty family uses the top open, so the
construction includes degree zero. The total exterior-algebra comparison is not used to
identify a homogeneous component.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ExteriorPower.Stalk

variable {X : RingedSpace.{u}} (F : X.Modules) (x : X) (n : ℕ)

/-- On a neighborhood, take the exterior power of the actual germ map; away from the point
the skyscraper value is zero. -/
def toSkyscraperApp (U : (Opens X)ᵒᵖ) :
    (presheaf F n).obj U ⟶
      (PresheafOfModules.Skyscraper.atPoint X.presheaf x
        ((stalkModuleCat F x).exteriorPower n)).obj U := by
  classical
  exact if hx : x ∈ U.unop then
    ModuleCat.exteriorPower.mapRestrictScalars
      (X.presheaf.germ U.unop x hx).hom
      (PresheafOfModules.germToStalk F.val x U.unop hx) n ≫
        eqToHom (PresheafOfModules.Skyscraper.obj_eq_of_mem X.presheaf x
          ((stalkModuleCat F x).exteriorPower n) U hx).symm
  else 0

/-- The exterior-power germ maps form a morphism of module presheaves. -/
def toSkyscraperPresheaf : presheaf F n ⟶
    PresheafOfModules.Skyscraper.atPoint X.presheaf x
      ((stalkModuleCat F x).exteriorPower n) where
  app := toSkyscraperApp F x n
  naturality := by sorry

/-- Sheafification extends the explicitly defined germ map. -/
def toSkyscraper : sheaf F n ⟶
    PresheafOfModules.Skyscraper.sheafAtPoint X.sheaf x
      ((stalkModuleCat F x).exteriorPower n) :=
  (PresheafOfModules.sheafificationHomEquiv
    (𝟙 X.ringCatSheaf.obj)).symm (toSkyscraperPresheaf F x n)

/-- The canonical forward homogeneous comparison from the stalk of the degree-`n` exterior
power sheaf to the exterior power of the stalk module. Its data is the stalk-skyscraper
adjunction applied to the concrete germ map above. -/
def comparison : stalkModuleCat (sheaf F n) x ⟶
    (stalkModuleCat F x).exteriorPower n :=
  (PresheafOfModules.Skyscraper.sheafHomEquiv X.sheaf x
    (sheaf F n) ((stalkModuleCat F x).exteriorPower n)).symm (toSkyscraper F x n)

/-- The forward comparison sends a local exterior generator to the exterior product of its
component germs. -/
theorem comparison_germ_mk (U : Opens X) (hx : x ∈ U)
    (m : Fin n → F.val.obj (op U)) :
    comparison F x n
      (TopCat.Presheaf.germ (sheaf F n).val.presheaf U x hx
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).unit.app (presheaf F n)).app (op U)
            (ModuleCat.exteriorPower.mk (R := X.presheaf.obj (op U))
              (M := F.val.obj (op U)) m))) =
      ModuleCat.exteriorPower.mk (R := X.presheaf.stalk x) (M := stalkModuleCat F x)
        (fun j ↦ TopCat.Presheaf.germ F.val.presheaf U x hx (m j)) := by
  sorry

/-- The germ of a local exterior product after the canonical sheafification unit. -/
def germWedge (U : Opens X) (hx : x ∈ U) (m : Fin n → F.val.obj (op U)) :
    stalkModuleCat (sheaf F n) x :=
  TopCat.Presheaf.germ (sheaf F n).val.presheaf U x hx
    (((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).unit.app (presheaf F n)).app (op U)
        (ModuleCat.exteriorPower.mk (R := X.presheaf.obj (op U))
          (M := F.val.obj (op U)) m))

/-- A common neighborhood for the finitely many chosen representatives. For degree zero this
is the top open. The representative chooser is the existing stalk owner, backed by mathlib's
proved germ-surjectivity theorem. -/
def commonOpen (m : Fin n → stalkModuleCat F x) : Opens X :=
  Finset.univ.inf fun j ↦
    (PresheafOfModules.Tensor.Stalk.representative x F.val (m j)).neighborhood

/-- The common neighborhood contains the stalk point, also for the empty family. -/
theorem mem_commonOpen (m : Fin n → stalkModuleCat F x) : x ∈ commonOpen F x n m := by
  classical
  have h : ∀ s : Finset (Fin n), x ∈ s.inf (fun j ↦
      (PresheafOfModules.Tensor.Stalk.representative x F.val (m j)).neighborhood) := by
    intro s
    induction s using Finset.induction_on with
    | empty => trivial
    | @insert i s hi ih =>
      simpa only [Finset.inf_insert, Opens.mem_inf] using
        And.intro (PresheafOfModules.Tensor.Stalk.representative x F.val (m i)).memNeighborhood ih
  exact h Finset.univ

/-- The common neighborhood lies in each representative's neighborhood. -/
theorem commonOpen_le (m : Fin n → stalkModuleCat F x) (j : Fin n) :
    commonOpen F x n m ≤
      (PresheafOfModules.Tensor.Stalk.representative x F.val (m j)).neighborhood := by
  classical
  exact Finset.inf_le (Finset.mem_univ j)

/-- Restrict each chosen germ representative to the common neighborhood. -/
def commonSection (m : Fin n → stalkModuleCat F x) (j : Fin n) :
    F.val.obj (op (commonOpen F x n m)) :=
  F.val.map (homOfLE (commonOpen_le F x n m j)).op
    (PresheafOfModules.Tensor.Stalk.representative x F.val (m j)).value

/-- Every common section has the originally specified germ. -/
theorem commonSection_germ (m : Fin n → stalkModuleCat F x) (j : Fin n) :
    TopCat.Presheaf.germ F.val.presheaf (commonOpen F x n m) x
      (mem_commonOpen F x n m) (commonSection F x n m j) = m j := by
  have hrep : TopCat.Presheaf.germ F.val.presheaf
      (PresheafOfModules.Tensor.Stalk.representative x F.val (m j)).neighborhood x
      (PresheafOfModules.Tensor.Stalk.representative x F.val (m j)).memNeighborhood
      (PresheafOfModules.Tensor.Stalk.representative x F.val (m j)).value = m j :=
    PresheafOfModules.Tensor.Stalk.representative_germ
      (R := X.presheaf) x F.val (m j)
  change TopCat.Presheaf.germ F.val.presheaf (commonOpen F x n m) x
    (mem_commonOpen F x n m)
    (F.val.presheaf.map (homOfLE (commonOpen_le F x n m j)).op
      (PresheafOfModules.Tensor.Stalk.representative x F.val (m j)).value) = m j
  exact (TopCat.Presheaf.germ_res_apply F.val.presheaf
    (homOfLE (commonOpen_le F x n m j)) x (mem_commonOpen F x n m) _).trans hrep

/-- The actual function underlying the inverse alternating map: take a local wedge on the
common neighborhood and then its germ. -/
def wedgeOfGerms (m : Fin n → stalkModuleCat F x) : stalkModuleCat (sheaf F n) x :=
  germWedge F x n (commonOpen F x n m) (mem_commonOpen F x n m)
    (commonSection F x n m)

/-- Choice independence and normalization: any simultaneous local representatives give the
same wedge germ. This statement also specifies the empty exterior product. -/
theorem wedgeOfGerms_germ (U : Opens X) (hx : x ∈ U)
    (m : Fin n → F.val.obj (op U)) :
    wedgeOfGerms F x n (fun j ↦ TopCat.Presheaf.germ F.val.presheaf U x hx (m j)) =
      germWedge F x n U hx m := by
  sorry

/-- The local-wedge-germ function is alternating and linear over the stalk ring. The
multilinear and alternating laws are Prop obligations, not data placeholders. -/
def germAlternatingMap : (stalkModuleCat F x).AlternatingMap
    (stalkModuleCat (sheaf F n) x) n :=
  { toMultilinearMap :=
      { toFun := wedgeOfGerms F x n
        map_update_add' := by sorry
        map_update_smul' := by sorry }
    map_eq_zero_of_eq' := by sorry }

/-- The explicit reverse homogeneous comparison, obtained by the universal property of the
`n`th exterior power applied to local wedge germs. -/
def comparisonInv : (stalkModuleCat F x).exteriorPower n ⟶
    stalkModuleCat (sheaf F n) x :=
  ModuleCat.exteriorPower.desc (germAlternatingMap F x n)

/-- The inverse sends the exterior product of arbitrary stalk elements to the concrete
common-neighborhood wedge germ. -/
theorem comparisonInv_mk (m : Fin n → stalkModuleCat F x) :
    comparisonInv F x n (ModuleCat.exteriorPower.mk m) = wedgeOfGerms F x n m := by
  exact ModuleCat.exteriorPower.desc_mk (germAlternatingMap F x n) m

/-- The inverse comparison sends a wedge of local germs to the germ of the local wedge. -/
theorem comparisonInv_germ_mk (U : Opens X) (hx : x ∈ U)
    (m : Fin n → F.val.obj (op U)) :
    comparisonInv F x n
        (ModuleCat.exteriorPower.mk
          (fun j ↦ TopCat.Presheaf.germ F.val.presheaf U x hx (m j))) =
      germWedge F x n U hx m := by
  rw [comparisonInv_mk, wedgeOfGerms_germ]

/-- The forward homogeneous comparison followed by the explicitly constructed reverse map. -/
theorem comparison_comp_comparisonInv :
    comparison F x n ≫ comparisonInv F x n = 𝟙 _ := by
  sorry

/-- The explicitly constructed reverse map followed by the forward homogeneous comparison. -/
theorem comparisonInv_comp_comparison :
    comparisonInv F x n ≫ comparison F x n = 𝟙 _ := by
  sorry

/-- The degreewise stalk isomorphism has two explicit data components. -/
def comparisonIso : stalkModuleCat (sheaf F n) x ≅
    (stalkModuleCat F x).exteriorPower n where
  hom := comparison F x n
  inv := comparisonInv F x n
  hom_inv_id := comparison_comp_comparisonInv F x n
  inv_hom_id := comparisonInv_comp_comparison F x n

end AlgebraicGeometry.RingedSpace.ExteriorPower.Stalk
