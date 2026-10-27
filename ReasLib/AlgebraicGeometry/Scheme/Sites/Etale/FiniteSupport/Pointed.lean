/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteSupport.Admissible
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteSupport.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteSupport.Presheaf
public import ReasLib.Topology.Opens.RelativeComplement
public import Mathlib.CategoryTheory.Category.Pointed
public import Mathlib.AlgebraicGeometry.Sites.Etale

/-!
# Pointed sections with admissible support

Pointed sections supported on an admissible locally closed subset form a diagram under restriction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}}

/-- A section is supported in `Z` when it is distinguished off `Z` in `U`. -/
def IsPointedSectionSupportedIn (f : X ⟶ Y) [LocallyQuasiFinite f]
    (F : Sheaf X.smallEtaleTopology Pointed.{u}) {W : Scheme.{u}} (hW : W ⟶ X) [Etale hW]
    (Z : LocallyCloseds W) (U : W.Opens) (h_subset : (Z : Set W) ⊆ U)
    (h_closed : IsClosed (U.ι ⁻¹' (Z : Set W)))
    (s : (F.1.obj (op (mk (U.ι ≫ hW)))).X) : Prop :=
  (F.1.map (FiniteSupport.homOfLE hW
      (TopologicalSpace.Opens.relativeComplement_le (U := U) (Z := (Z : Set W))
        (by change IsClosed (U.ι ⁻¹' (Z : Set W)); exact h_closed))).op).toFun s =
    (F.1.obj (op (mk (Scheme.Opens.ι (TopologicalSpace.Opens.relativeComplement U (Z : Set W)
      (by change IsClosed (U.ι ⁻¹' (Z : Set W)); exact h_closed)) ≫ hW)))).point

/-- The pointed set of sections supported on an admissible closed subset. -/
def pointedSectionsSupportedIn (f : X ⟶ Y) [LocallyQuasiFinite f]
    (F : Sheaf X.smallEtaleTopology Pointed.{u}) {V : Y.Etale}
    (A : FiniteSupport.Admissible f V) : Pointed.{u} :=
  Pointed.of
    (⟨(F.1.obj (op (mk (A.ambient.ι ≫ baseChangeToSource f V)))).point, sorry⟩ :
      { s : (F.1.obj (op (mk (A.ambient.ι ≫ baseChangeToSource f V)))).X //
        IsPointedSectionSupportedIn f F (baseChangeToSource f V) A.subset A.ambient
          A.subset_le_ambient A.isClosed_in_ambient s })

/-- Membership in the supported pointed set is precisely the support condition. -/
theorem mem_pointedSectionsSupportedIn_iff (f : X ⟶ Y) [LocallyQuasiFinite f]
    (F : Sheaf X.smallEtaleTopology Pointed.{u}) {V : Y.Etale}
    (A : FiniteSupport.Admissible f V)
    (s : (F.1.obj (op (mk (A.ambient.ι ≫ baseChangeToSource f V)))).X) :
    IsPointedSectionSupportedIn f F (baseChangeToSource f V) A.subset A.ambient
        A.subset_le_ambient A.isClosed_in_ambient s ↔
      (F.1.map (FiniteSupport.homOfLE (baseChangeToSource f V)
          (TopologicalSpace.Opens.relativeComplement_le (U := A.ambient) (Z := (A.subset : Set _))
            (by change IsClosed (A.ambient.ι ⁻¹' (A.subset : Set _)); exact A.isClosed_in_ambient))).op).toFun s =
        (F.1.obj (op (mk (Scheme.Opens.ι (TopologicalSpace.Opens.relativeComplement A.ambient (A.subset : Set _)
            (by change IsClosed (A.ambient.ι ⁻¹' (A.subset : Set _)); exact A.isClosed_in_ambient)) ≫
          baseChangeToSource f V)))).point := Iff.rfl

/-- Restriction of supported pointed sections along an inclusion of supports. -/
def pointedSectionsSupportedInMap (f : X ⟶ Y) [LocallyQuasiFinite f]
    (F : Sheaf X.smallEtaleTopology Pointed.{u}) {V : Y.Etale}
    {A B : FiniteSupport.Admissible f V} (h : A ≤ B) :
    pointedSectionsSupportedIn f F A ⟶ pointedSectionsSupportedIn f F B where
  toFun s := ⟨(F.1.map (FiniteSupport.homOfLE (baseChangeToSource f V) h.2).op).toFun s.1, sorry⟩
  map_point := sorry

/-- The diagram of supported pointed sections indexed by admissible supports. -/
def pointedAdmissibleDiagram (f : X ⟶ Y) [LocallyQuasiFinite f]
    (F : Sheaf X.smallEtaleTopology Pointed.{u}) (V : Y.Etale) :
    FiniteSupport.Admissible f V ⥤ Pointed.{u} where
  obj := pointedSectionsSupportedIn f F
  map h := pointedSectionsSupportedInMap f F (leOfHom h)
  map_id := sorry
  map_comp := sorry

/-- Restriction of the supported-section diagram under base change in `Y`. -/
def pointedAdmissibleRestriction (f : X ⟶ Y) [LocallyQuasiFinite f]
    (F : Sheaf X.smallEtaleTopology Pointed.{u}) {V' V : Y.Etale} (g : V' ⟶ V) :
    pointedAdmissibleDiagram f F V ⟶
      FiniteSupport.Admissible.pullbackFunctor f g ⋙ pointedAdmissibleDiagram f F V' where
  app A :=
    { toFun := fun s ↦ ⟨(F.1.map (FiniteSupport.preimageHom f g A.ambient).op).toFun s.1, sorry⟩
      map_point := sorry }
  naturality := sorry

end AlgebraicGeometry.Scheme.Etale

end
