/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint

open CategoryTheory Opposite
open AlgebraicGeometry

universe u

@[expose] public section

noncomputable section

namespace AlgebraicGeometry.Scheme.Etale

variable {S : Scheme.{u}}

/-- A section vanishes on an open when its restriction to the corresponding étale subobject is
zero. -/
def vanishesOn (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) (U : S.Etale)
    (σ : F.1.obj (op U)) (W : U.left.Opens) : Prop :=
  F.1.map
      (MorphismProperty.Over.homMk W.ι :
        (Scheme.Etale.mk (W.ι ≫ U.hom) : S.Etale) ⟶ U).op σ = 0

/-- The small-étale point induced by a geometric point of the underlying scheme of an étale
object. -/
noncomputable def geometricStalkPoint (U : S.Etale)
    (ū : Scheme.GeometricPoint U.left) : (S.smallEtaleTopology).Point :=
  @Scheme.pointSmallEtale S ū.K inferInstance
    (@IsSepClosed.of_isAlgClosed ū.K inferInstance ū.isAlgClosed) (ū.hom ≫ U.hom)

/-- The value of a local section in the geometric stalk determined by a geometric point. -/
noncomputable def geometricGerm (U : S.Etale)
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u})
    (σ : F.1.obj (op U)) (ū : Scheme.GeometricPoint U.left) :
    (((geometricStalkPoint U ū).presheafFiber :
      (S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).obj F.1 : Type u) :=
  (geometricStalkPoint U ū).toPresheafFiber U
    (Over.homMk ū.hom :
      Over.mk (ū.hom ≫ U.hom) ⟶ (Scheme.Etale.forget S).obj U) F.1 σ

/-- A local section has a largest Zariski open on which it vanishes. -/
theorem exists_largest_vanishing_open
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) (U : S.Etale)
    (σ : F.1.obj (op U)) :
    ∃ W : U.left.Opens, vanishesOn F U σ W ∧
      ∀ V : U.left.Opens, vanishesOn F U σ V → V ≤ W := sorry

/-- For an étale morphism, a section vanishes after restriction exactly when its image lies in an
open on which it vanishes maximally. -/
theorem restrict_eq_zero_iff_image_subset
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) (U : S.Etale)
    (σ : F.1.obj (op U)) (W : U.left.Opens)
    (hW : vanishesOn F U σ W)
    (hmax : ∀ V : U.left.Opens, vanishesOn F U σ V → V ≤ W)
    {V : S.Etale} (φ : V ⟶ U) :
    F.1.map φ.op σ = 0 ↔ Set.range φ.left ⊆ (W : Set U.left) := sorry

/-- A geometric germ vanishes exactly at the geometric points contained in the maximal vanishing
open. -/
theorem geometric_germ_eq_zero_iff_mem
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) (U : S.Etale)
    (σ : F.1.obj (op U)) (W : U.left.Opens)
    (hW : vanishesOn F U σ W)
    (hmax : ∀ V : U.left.Opens, vanishesOn F U σ V → V ≤ W)
    (ū : Scheme.GeometricPoint U.left) :
    geometricGerm U F σ ū = 0 ↔ ū.image ∈ W := sorry

end AlgebraicGeometry.Scheme.Etale

end
