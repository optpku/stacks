/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.RingTheory.FreeRing
public import ReasLib.CategoryTheory.Sites.Over.SheafCompose
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Relocalization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fppf.Comparison

/-! # Module sheafification on big algebraic-space sites -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u v w

private theorem moduleSheafification_hasSheafCompose
    {C : Type v} [Category.{w} C] (J : GrothendieckTopology C) :
    J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u}) := by
  -- The underlying-set functor is represented by the free ring on one generator,
  -- so it preserves limits even when the site is larger than the rings.
  let e : coyoneda.obj (op (RingCat.of (FreeRing PUnit.{u + 1}))) ≅
      forget RingCat.{u} :=
    NatIso.ofComponents (fun R ↦ Equiv.toIso
      { toFun := fun α ↦ α.hom (FreeRing.of PUnit.unit)
        invFun := fun r ↦ RingCat.ofHom (FreeRing.lift (fun _ ↦ r))
        left_inv := fun α ↦ by
          apply RingCat.hom_ext
          apply FreeRing.hom_ext
          intro x
          cases x
          exact FreeRing.lift_of _ _
        right_inv := fun r ↦ FreeRing.lift_of _ _ })
      (fun α ↦ by ext g; rfl)
  letI : PreservesLimitsOfSize.{w, max v w} (forget RingCat.{u}) :=
    preservesLimits_of_natIso e
  constructor
  intro P hP
  apply Presheaf.isSheaf_of_isSheaf_comp J _ (forget AddCommGrpCat.{u})
  exact Presheaf.isSheaf_comp_of_isSheaf J P (forget RingCat.{u}) hP

-- Use Mathlib's proved continuity of dense subsites, without the additional
-- proof debt in the special-cocontinuity bridge.
attribute [-instance] Functor.IsDenseSubsite.isSpecialCocontinuous in
private instance moduleSheafification_iteratedSlice_isEquivalence
    {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
    {X : C} (U : Over X) (A : Type*) [Category* A] :
    (U.iteratedSliceEquiv.inverse.sheafPushforwardContinuous A
      (J.over U.left) ((J.over X).over U)).IsEquivalence :=
  (U.iteratedSliceEquiv.sheafCongr ((J.over X).over U) (J.over U.left) A).isEquivalence_functor

namespace AlgebraicGeometry.AlgebraicSpace.Etale

variable {S : Scheme.{u}}

/-- Abelian-group-valued sheaf composition exists on `(Spaces/X)_étale`. -/
instance overEtaleTopology_hasSheafCompose (X : AlgebraicSpace S) :
    (overEtaleTopology X).HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  moduleSheafification_hasSheafCompose _

/-- Abelian-group-valued weak sheafification exists on `(Spaces/X)_étale`. -/
instance overEtaleTopology_hasWeakSheafify (X : AlgebraicSpace S) :
    HasWeakSheafify (overEtaleTopology X) AddCommGrpCat.{u} :=
  sorry

/-- On `(Spaces/X)_étale`, sheafification equivalences are the locally bijective
morphisms. -/
instance overEtaleTopology_wEqualsLocallyBijective (X : AlgebraicSpace S) :
    (overEtaleTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  sorry

/-- Abelian-group-valued sheaf composition exists on every slice of
`(Spaces/X)_étale`. -/
instance overEtaleTopology_over_hasSheafCompose (X : AlgebraicSpace S) :
    ∀ U : Over X,
      ((overEtaleTopology X).over U).HasSheafCompose
        (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  fun U ↦ GrothendieckTopology.HasSheafCompose.over
    (overEtaleTopology X) (forget₂ RingCat.{u} AddCommGrpCat.{u}) U

attribute [-instance] Functor.IsDenseSubsite.isSpecialCocontinuous in
/-- Abelian-group-valued weak sheafification exists on every slice of
`(Spaces/X)_étale`. -/
instance overEtaleTopology_over_hasWeakSheafify (X : AlgebraicSpace S) :
    ∀ U : Over X,
      HasWeakSheafify ((overEtaleTopology X).over U) AddCommGrpCat.{u} :=
  fun U ↦ Functor.IsDenseSubsite.hasWeakSheafify_of_isEquivalence
    (overEtaleTopology U.left) ((overEtaleTopology X).over U)
    U.iteratedSliceEquiv.inverse AddCommGrpCat.{u}

attribute [-instance] Functor.IsDenseSubsite.isSpecialCocontinuous in
/-- On every slice of `(Spaces/X)_étale`, sheafification equivalences are the
locally bijective morphisms. -/
instance overEtaleTopology_over_wEqualsLocallyBijective (X : AlgebraicSpace S) :
    ∀ U : Over X,
      ((overEtaleTopology X).over U).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  fun U ↦ GrothendieckTopology.WEqualsLocallyBijective.transport
    ((overEtaleTopology X).over U) (overEtaleTopology U.left)
    U.iteratedSliceEquiv.inverse (Functor.IsDenseSubsite.coverPreserving _ _ _)

end AlgebraicGeometry.AlgebraicSpace.Etale

namespace AlgebraicGeometry.AlgebraicSpace.Fppf

variable {S : Scheme.{u}}

/-- Abelian-group-valued sheaf composition exists on `(Spaces/X)_fppf`. -/
instance overFppfTopology_hasSheafCompose (X : AlgebraicSpace S) :
    (overFppfTopology X).HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  moduleSheafification_hasSheafCompose _

/-- Abelian-group-valued weak sheafification exists on `(Spaces/X)_fppf`. -/
instance overFppfTopology_hasWeakSheafify (X : AlgebraicSpace S) :
    HasWeakSheafify (overFppfTopology X) AddCommGrpCat.{u} :=
  sorry

/-- On `(Spaces/X)_fppf`, sheafification equivalences are the locally bijective
morphisms. -/
instance overFppfTopology_wEqualsLocallyBijective (X : AlgebraicSpace S) :
    (overFppfTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  sorry

/-- Abelian-group-valued sheaf composition exists on every slice of
`(Spaces/X)_fppf`. -/
instance overFppfTopology_over_hasSheafCompose (X : AlgebraicSpace S) :
    ∀ U : Over X,
      ((overFppfTopology X).over U).HasSheafCompose
        (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  fun U ↦ GrothendieckTopology.HasSheafCompose.over
    (overFppfTopology X) (forget₂ RingCat.{u} AddCommGrpCat.{u}) U

attribute [-instance] Functor.IsDenseSubsite.isSpecialCocontinuous in
/-- Abelian-group-valued weak sheafification exists on every slice of
`(Spaces/X)_fppf`. -/
instance overFppfTopology_over_hasWeakSheafify (X : AlgebraicSpace S) :
    ∀ U : Over X,
      HasWeakSheafify ((overFppfTopology X).over U) AddCommGrpCat.{u} :=
  fun U ↦ Functor.IsDenseSubsite.hasWeakSheafify_of_isEquivalence
    (overFppfTopology U.left) ((overFppfTopology X).over U)
    U.iteratedSliceEquiv.inverse AddCommGrpCat.{u}

attribute [-instance] Functor.IsDenseSubsite.isSpecialCocontinuous in
/-- On every slice of `(Spaces/X)_fppf`, sheafification equivalences are the
locally bijective morphisms. -/
instance overFppfTopology_over_wEqualsLocallyBijective (X : AlgebraicSpace S) :
    ∀ U : Over X,
      ((overFppfTopology X).over U).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  fun U ↦ GrothendieckTopology.WEqualsLocallyBijective.transport
    ((overFppfTopology X).over U) (overFppfTopology U.left)
    U.iteratedSliceEquiv.inverse (Functor.IsDenseSubsite.coverPreserving _ _ _)

end AlgebraicGeometry.AlgebraicSpace.Fppf

end

end
