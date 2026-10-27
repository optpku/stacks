/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.Morphism
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory

noncomputable section

universe u v w z

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

private theorem hasSheafify_addCommGrpCat_of_univLE
    {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
    [UnivLE.{max v w, z}] : HasSheafify J AddCommGrpCat.{z} := by
  have : Small.{z} C :=
    @Small.trans_univLE.{max v w, z, v} C (small_max.{w} C) inferInstance
  have : LocallySmall.{z} C :=
    ⟨fun U V => @Small.trans_univLE.{max v w, z, w} (U ⟶ V)
      (small_max.{v} (U ⟶ V)) inferInstance⟩
  let e : C ≌ SmallModel.{z} C := equivSmallModel C
  exact e.hasSheafify J (e.inverse.inducedTopology J) AddCommGrpCat.{z}

/-- The lisse-étale inclusion is continuous for the lisse-étale topology and the
associated étale topology. -/
instance lisseEtaleInclusion.instIsContinuous (X : GroupoidsOver S) [AlgebraicStack X] :
    (lisseEtaleInclusion X).IsContinuous (lisseEtaleTopology X) X.etaleTopology :=
  sorry

/-- The lisse-étale inclusion is cocontinuous for the lisse-étale topology and the
associated étale topology. -/
instance lisseEtaleInclusion.instIsCocontinuous (X : GroupoidsOver S) [AlgebraicStack X] :
    (lisseEtaleInclusion X).IsCocontinuous (lisseEtaleTopology X) X.etaleTopology :=
  sorry

/-- The flat-fppf inclusion is continuous into the inherited fppf topology. -/
instance flatFppfInclusion.instIsContinuous (X : GroupoidsOver S) [AlgebraicStack X] :
    (flatFppfInclusion X).IsContinuous (flatFppfTopology X) (inheritedFppfTopology X) :=
  sorry

/-- The flat-fppf inclusion is cocontinuous into the inherited fppf topology. -/
instance flatFppfInclusion.instIsCocontinuous (X : GroupoidsOver S) [AlgebraicStack X] :
    (flatFppfInclusion X).IsCocontinuous (flatFppfTopology X) (inheritedFppfTopology X) :=
  sorry

/-- Sheafification of abelian sheaves on the associated étale site. -/
instance (priority := 1100) etaleTopology_hasSheafify (Z : GroupoidsOver S) [AlgebraicStack Z] [UnivLE.{u + 1, z}] :
    HasSheafify Z.etaleTopology AddCommGrpCat.{z} :=
  hasSheafify_addCommGrpCat_of_univLE _

/-- Sheafification of abelian sheaves on the lisse-étale site. -/
instance lisseEtaleTopology_hasSheafify (Z : GroupoidsOver S) [AlgebraicStack Z] [UnivLE.{u + 1, z}] :
    HasSheafify (lisseEtaleTopology Z) AddCommGrpCat.{z} :=
  hasSheafify_addCommGrpCat_of_univLE _

/-- Sheafification of abelian sheaves on the inherited fppf site. -/
instance inheritedFppfTopology_hasSheafify (Z : GroupoidsOver S) [UnivLE.{u + 1, z}] :
    HasSheafify (inheritedFppfTopology Z) AddCommGrpCat.{z} :=
  hasSheafify_addCommGrpCat_of_univLE _

/-- Sheafification of abelian sheaves on the flat-fppf site. -/
instance flatFppfTopology_hasSheafify (Z : GroupoidsOver S) [AlgebraicStack Z] [UnivLE.{u + 1, z}] :
    HasSheafify (flatFppfTopology Z) AddCommGrpCat.{z} :=
  hasSheafify_addCommGrpCat_of_univLE _

/-- The inclusion of abelian sheaves into presheaves on the associated étale
site admits a left adjoint at any coefficient universe bounding the site. -/
instance (priority := 1100) etaleTopology_hasWeakSheafify (Z : GroupoidsOver S)
    [AlgebraicStack Z] [UnivLE.{u + 1, z}] :
    HasWeakSheafify Z.etaleTopology AddCommGrpCat.{z} :=
  HasSheafify.isRightAdjoint

/-- The inclusion of abelian sheaves into presheaves on the lisse-étale
site admits a left adjoint at any coefficient universe bounding the site. -/
instance (priority := 1100) lisseEtaleTopology_hasWeakSheafify_of_univLE (Z : GroupoidsOver S)
    [AlgebraicStack Z] [UnivLE.{u + 1, z}] :
    HasWeakSheafify (lisseEtaleTopology Z) AddCommGrpCat.{z} :=
  HasSheafify.isRightAdjoint

/-- The inclusion of abelian sheaves into presheaves on the inherited fppf
site admits a left adjoint at any coefficient universe bounding the site. -/
instance (priority := 1100) inheritedFppfTopology_hasWeakSheafify (Z : GroupoidsOver S)
    [UnivLE.{u + 1, z}] :
    HasWeakSheafify (inheritedFppfTopology Z) AddCommGrpCat.{z} :=
  HasSheafify.isRightAdjoint

/-- The inclusion of abelian sheaves into presheaves on the flat-fppf
site admits a left adjoint at any coefficient universe bounding the site. -/
instance (priority := 1100) flatFppfTopology_hasWeakSheafify_of_univLE (Z : GroupoidsOver S)
    [AlgebraicStack Z] [UnivLE.{u + 1, z}] :
    HasWeakSheafify (flatFppfTopology Z) AddCommGrpCat.{z} :=
  HasSheafify.isRightAdjoint

/-- Left Kan extensions of abelian presheaves along the lisse-étale inclusion. -/
instance lisseEtaleInclusion.op_hasLeftKanExtension (Z : GroupoidsOver S)
    [AlgebraicStack Z] (P : (lisseEtaleSite Z)ᵒᵖ ⥤ AddCommGrpCat.{z})
    [UnivLE.{u + 1, z}] :
    (lisseEtaleInclusion Z).op.HasLeftKanExtension P := by
  letI : Limits.HasColimitsOfSize.{u + 1, u + 1} AddCommGrpCat.{z} :=
    Limits.hasColimitsOfSizeOfUnivLE _
  letI : Limits.HasColimitsOfSize.{u, u + 1} AddCommGrpCat.{z} :=
    Limits.hasColimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} _
  infer_instance

/-- Left Kan extensions of abelian presheaves along the flat-fppf inclusion. -/
instance flatFppfInclusion.op_hasLeftKanExtension (Z : GroupoidsOver S)
    [AlgebraicStack Z] (P : (flatFppfSite Z)ᵒᵖ ⥤ AddCommGrpCat.{z})
    [UnivLE.{u + 1, z}] :
    (flatFppfInclusion Z).op.HasLeftKanExtension P := by
  letI : Limits.HasColimitsOfSize.{u + 1, u + 1} AddCommGrpCat.{z} :=
    Limits.hasColimitsOfSizeOfUnivLE _
  letI : Limits.HasColimitsOfSize.{u, u + 1} AddCommGrpCat.{z} :=
    Limits.hasColimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} _
  infer_instance

end AlgebraicGeometry.AlgebraicStack
