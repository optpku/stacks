/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.AbelianPullback

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The canonical comparison from the pullback of a constant sheaf to the constant sheaf. -/
noncomputable def constantSheaf_sheafPullback_hom
    {Z Z' : Scheme.{u}} (p : Z' ⟶ Z) (M : AddCommGrpCat.{u}) :
    (etaleAbelianSheafPullback p).obj
      ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u}).obj M) ⟶
    (constantSheaf Z'.smallEtaleTopology AddCommGrpCat.{u}).obj M :=
  (((smallEtalePullback p).sheafAdjunctionContinuous AddCommGrpCat.{u}
        Z.smallEtaleTopology Z'.smallEtaleTopology).homEquiv
      ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u}).obj M)
      ((constantSheaf Z'.smallEtaleTopology AddCommGrpCat.{u}).obj M)).symm
    (((sheafificationAdjunction Z.smallEtaleTopology AddCommGrpCat.{u}).homEquiv
        ((Functor.const _).obj M)
        (((smallEtalePullback p).sheafPushforwardContinuous AddCommGrpCat.{u}
            Z.smallEtaleTopology Z'.smallEtaleTopology).obj
          ((constantSheaf Z'.smallEtaleTopology AddCommGrpCat.{u}).obj M))).symm
      ((Functor.constCompWhiskeringLeftIso (Z.Etaleᵒᵖ) (C := AddCommGrpCat.{u})
          (smallEtalePullback p).op).inv.app M ≫
        Functor.whiskerLeft (smallEtalePullback p).op
          ((sheafificationAdjunction Z'.smallEtaleTopology AddCommGrpCat.{u}).unit.app
            ((Functor.const _).obj M))))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The comparison from the pullback of a constant sheaf to the constant sheaf is an isomorphism. -/
public instance isIso_constantSheaf_sheafPullback_hom
    {Z Z' : Scheme.{u}} {p : Z' ⟶ Z} {M : AddCommGrpCat.{u}} :
    IsIso (constantSheaf_sheafPullback_hom p M) :=
  by
    let terminal := MorphismProperty.Over.mkIdTerminal (@Etale) Z
    let imageTerminal := IsTerminal.ofIso
      (MorphismProperty.Over.mkIdTerminal (@Etale) Z')
      (Etale.globalEtalePullbackIso p).symm
    let sourceAdj := (constantSheafAdj Z.smallEtaleTopology AddCommGrpCat.{u} terminal).comp
      ((smallEtalePullback p).sheafAdjunctionContinuous AddCommGrpCat.{u}
        Z.smallEtaleTopology Z'.smallEtaleTopology)
    let targetAdj := constantSheafAdj Z'.smallEtaleTopology AddCommGrpCat.{u} imageTerminal
    have comparison_eq : constantSheaf_sheafPullback_hom p M =
        (sourceAdj.leftAdjointUniq targetAdj).hom.app M := by
      apply (sourceAdj.homEquiv _ _).injective
      rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
      simp [sourceAdj, targetAdj, constantSheaf_sheafPullback_hom,
        constantSheafAdj, constantPresheafAdj, Adjunction.comp_homEquiv]
      erw [Equiv.apply_symm_apply]
      erw [Adjunction.homEquiv_unit]
      change 𝟙 M ≫ (𝟙 M ≫ _) = _
      simp only [Category.id_comp]
      rfl
    rw [comparison_eq]
    exact ((sourceAdj.leftAdjointUniq targetAdj).app M).isIso_hom

/-- Sheaf pullback of a constant abelian sheaf is canonically isomorphic to the same constant sheaf. -/
noncomputable def constantSheaf_sheafPullback
    {Z Z' : Scheme.{u}} (p : Z' ⟶ Z) (M : AddCommGrpCat.{u}) :
    (etaleAbelianSheafPullback p).obj
        ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u}).obj M) ≅
      (constantSheaf Z'.smallEtaleTopology AddCommGrpCat.{u}).obj M :=
  asIso (constantSheaf_sheafPullback_hom p M)

/-- The pullback map on small-étale cohomology of a constant abelian sheaf. -/
noncomputable def etaleHq_constant_pullback
    {Z Z' : Scheme.{u}} (p : Z' ⟶ Z) (M : AddCommGrpCat.{u}) (q : ℕ) :
    (Sheaf.functorH Z.smallEtaleTopology q).obj
      ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u}).obj M) ⟶
    (Sheaf.functorH Z'.smallEtaleTopology q).obj
      ((constantSheaf Z'.smallEtaleTopology AddCommGrpCat.{u}).obj M) :=
  AddCommGrpCat.ofHom
    ((etaleAbelianSheafPullback p).mapExtAddHom
      ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift ℤ)))
      ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u}).obj M) q) ≫
    AddCommGrpCat.ofHom
      (((Abelian.extFunctor q).map
          (inv (constantSheaf_sheafPullback_hom p
            (AddCommGrpCat.of (ULift ℤ)))).op).app
        ((etaleAbelianSheafPullback p).obj
          ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u}).obj M))).hom ≫
    (Sheaf.functorH Z'.smallEtaleTopology q).map
      (constantSheaf_sheafPullback_hom p M)

end AlgebraicGeometry.Scheme.Hom
