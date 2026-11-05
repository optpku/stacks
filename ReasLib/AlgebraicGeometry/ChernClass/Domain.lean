/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Topology.Clopen
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Category.Ring.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.AssociatedSheaf
public import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Pullback

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped BigOperators

noncomputable section

universe u v w x

namespace AlgebraicGeometry.ChernClass

/-- The open complement of a clopen subscheme. -/
def clopenComplement {X : Scheme.{u}} (U : X.Opens)
    (hU : IsClopen (U : Set X)) : X.Opens :=
  ⟨(U : Set X)ᶜ, hU.compl.isOpen⟩

/-- The carrier of `clopenComplement U hU` is the complement of the carrier of `U`. -/
theorem coe_clopenComplement {X : Scheme.{u}} (U : X.Opens)
    (hU : IsClopen (U : Set X)) :
    (clopenComplement U hU : Set X) = (U : Set X)ᶜ := rfl

/-- The Picard class of the tautological invertible module of a projective bundle. -/
noncomputable def tautologicalPicardClass {X P : Scheme.{u}} (p : P ⟶ X)
    (E : X.Modules) (hP : Scheme.ProjectiveBundle.Representation p E) :
    P.PicardGroup :=
  @Scheme.Modules.picardClass P
    (Scheme.ProjectiveBundle.tautologicalSheaf p hP)
    (Scheme.ProjectiveBundle.tautologicalSheaf_isInvertible p hP)

/-- The tautological Picard class is represented by the tautological invertible module. -/
theorem tautologicalPicardClass_eq {X P : Scheme.{u}} (p : P ⟶ X)
    (E : X.Modules) (hP : Scheme.ProjectiveBundle.Representation p E) :
    tautologicalPicardClass p E hP =
      @Scheme.Modules.picardClass P
        (Scheme.ProjectiveBundle.tautologicalSheaf p hP)
        (Scheme.ProjectiveBundle.tautologicalSheaf_isInvertible p hP) := rfl

/-- The geometric domain of Stacks 0FI4: qcqs schemes, closed under clopen restrictions,
projective bundles, their base changes, and quotient inclusions (the three conditions preceding
the five cohomology axioms). The Cartier property of a corank-one quotient is retained as a
supplied geometric property until its scheme-level theorem has been proved. No cohomology
ring or first Chern class is part of this domain. -/
structure Domain
    {C : Type u} [Category.{v} C] (toScheme : C ⥤ Scheme.{w}) where
  /-- Every scheme in the source category is quasi-compact. -/
  compactSpace : ∀ X, CompactSpace (toScheme.obj X)
  /-- Every scheme in the source category is quasi-separated. -/
  quasiSeparatedSpace : ∀ X, QuasiSeparatedSpace (toScheme.obj X)
  /-- The object of the category presenting a clopen subscheme. -/
  clopenObject : ∀ (X : C) (U : (toScheme.obj X).Opens),
    IsClopen (U : Set (toScheme.obj X)) → C
  /-- The chosen category object really presents the clopen subscheme. -/
  clopenIso : ∀ (X : C) (U : (toScheme.obj X).Opens)
      (hU : IsClopen (U : Set (toScheme.obj X))),
    toScheme.obj (clopenObject X U hU) ≅ U.toScheme
  /-- The clopen inclusion is a morphism of the source category. -/
  clopenInclusion : ∀ (X : C) (U : (toScheme.obj X).Opens)
      (hU : IsClopen (U : Set (toScheme.obj X))),
    clopenObject X U hU ⟶ X
  /-- The chosen clopen inclusion maps to the usual scheme inclusion. -/
  clopenInclusion_map : ∀ (X : C) (U : (toScheme.obj X).Opens)
      (hU : IsClopen (U : Set (toScheme.obj X))),
    toScheme.map (clopenInclusion X U hU) = (clopenIso X U hU).hom ≫ U.ι
  /-- A source-category morphism factoring through a clopen subscheme has a factor in the
  source category. -/
  clopenFactor : ∀ {X' X : C} (f : X' ⟶ X) (U : (toScheme.obj X).Opens)
      (hU : IsClopen (U : Set (toScheme.obj X)))
      (g : toScheme.obj X' ⟶ U.toScheme),
    g ≫ U.ι = toScheme.map f → (X' ⟶ clopenObject X U hU)
  /-- The chosen categorical factor maps to the given factor through the clopen subscheme. -/
  clopenFactor_map : ∀ {X' X : C} (f : X' ⟶ X)
      (U : (toScheme.obj X).Opens) (hU : IsClopen (U : Set (toScheme.obj X)))
      (g : toScheme.obj X' ⟶ U.toScheme) (h_g : g ≫ U.ι = toScheme.map f),
    toScheme.map (clopenFactor f U hU g h_g) = g ≫ (clopenIso X U hU).inv
  /-- The object presenting the projective bundle of a finite locally free module. -/
  projectiveBundle : ∀ (X : C),
    ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty (toScheme.obj X).Modules) → C
  /-- The projection from the chosen projective bundle. -/
  projectiveBundleProjection : ∀ (X : C)
      (E : ObjectProperty.FullSubcategory
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty (toScheme.obj X).Modules)),
    projectiveBundle X E ⟶ X
  /-- The chosen projection represents the projective bundle of `E`. -/
  projectiveBundleRepresentation : ∀ (X : C)
      (E : ObjectProperty.FullSubcategory
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty (toScheme.obj X).Modules)),
    Scheme.ProjectiveBundle.Representation
      (toScheme.map (projectiveBundleProjection X E)) E.obj
  /-- Base change of a projective bundle is a morphism in the source category. -/
  projectiveBundlePullback : ∀ {X' X : C} (f : X' ⟶ X)
      (E : ObjectProperty.FullSubcategory
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty (toScheme.obj X).Modules)),
    projectiveBundle X'
        (Scheme.VectorBundleK0.pullbackObj (toScheme.map f) E) ⟶
      projectiveBundle X E
  /-- The chosen base-change arrow classifies the tautological quotient of the pulled-back
  bundle, transported along the canonical comparison for composite pullback. -/
  projectiveBundlePullback_map : ∀ {X' X : C} (f : X' ⟶ X)
      (E : ObjectProperty.FullSubcategory
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty (toScheme.obj X).Modules)),
    let E' := Scheme.VectorBundleK0.pullbackObj (toScheme.map f) E
    let p' := toScheme.map (projectiveBundleProjection X' E')
    toScheme.map (projectiveBundlePullback f E) =
      (((projectiveBundleRepresentation X E).liftEquiv (p' ≫ toScheme.map f)).symm
        (InvertibleQuotient.IsoClass.mk (InvertibleQuotient.precomposeIso
          ((Scheme.Modules.pullbackComp p' (toScheme.map f)).app E.obj).symm
          (Scheme.ProjectiveBundle.tautologicalQuotient p'
            (projectiveBundleRepresentation X' E'))))).hom
  /-- The projective-bundle base-change morphism lies over the original morphism. -/
  projectiveBundlePullback_comm : ∀ {X' X : C} (f : X' ⟶ X)
      (E : ObjectProperty.FullSubcategory
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty (toScheme.obj X).Modules)),
    toScheme.map (projectiveBundlePullback f E) ≫
        toScheme.map (projectiveBundleProjection X E) =
      toScheme.map (projectiveBundleProjection X'
        (Scheme.VectorBundleK0.pullbackObj (toScheme.map f) E)) ≫ toScheme.map f
  /-- The square defining projective-bundle base change is cartesian. -/
  projectiveBundlePullback_isPullback : ∀ {X' X : C} (f : X' ⟶ X)
      (E : ObjectProperty.FullSubcategory
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty (toScheme.obj X).Modules)),
    IsPullback (toScheme.map (projectiveBundlePullback f E))
      (toScheme.map (projectiveBundleProjection X'
        (Scheme.VectorBundleK0.pullbackObj (toScheme.map f) E)))
      (toScheme.map (projectiveBundleProjection X E)) (toScheme.map f)
  /-- A quotient of finite locally free modules induces a morphism of projective bundles in
  the source category. -/
  projectiveBundleQuotient : ∀ {X : C}
      {E F : ObjectProperty.FullSubcategory
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty (toScheme.obj X).Modules)}
      (q : E ⟶ F), Epi q.hom → (projectiveBundle X F ⟶ projectiveBundle X E)
  /-- The chosen quotient arrow classifies the pullback of the supplied surjection followed
  by the tautological quotient of `F`. Surjectivity is in the category of module sheaves. -/
  projectiveBundleQuotient_map : ∀ {X : C}
      {E F : ObjectProperty.FullSubcategory
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty (toScheme.obj X).Modules)}
      (q : E ⟶ F) (h_q : Epi q.hom),
    let p' := toScheme.map (projectiveBundleProjection X F)
    let t := Scheme.ProjectiveBundle.tautologicalQuotient p'
      (projectiveBundleRepresentation X F)
    toScheme.map (projectiveBundleQuotient q h_q) =
      (((projectiveBundleRepresentation X E).liftEquiv p').symm
        (InvertibleQuotient.IsoClass.mk
          { object := t.object
            isInvertible := t.isInvertible
            hom := (Scheme.Modules.pullback p').map q.hom ≫ t.hom
            hom_epi := epi_comp'
              (@Functor.map_epi _ _ _ _ (Scheme.Modules.pullback p') inferInstance
                _ _ q.hom h_q) t.hom_epi })).hom
  /-- The projective-bundle morphism induced by a quotient is a closed immersion. -/
  projectiveBundleQuotient_isClosed : ∀ {X : C}
      {E F : ObjectProperty.FullSubcategory
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty (toScheme.obj X).Modules)}
      (q : E ⟶ F) (h_q : Epi q.hom),
    IsClosedImmersion (toScheme.map (projectiveBundleQuotient q h_q))
  /-- The projective-bundle inclusion induced by a corank-one quotient is an effective Cartier
  divisor. -/
  quotient_isEffectiveCartier : ∀ (X : C)
      (E F : ObjectProperty.FullSubcategory
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty (toScheme.obj X).Modules))
      (r : ℕ) (h_E : Scheme.Modules.IsFiniteLocallyFreeOfRank (r + 1) E.obj)
      (h_F : Scheme.Modules.IsFiniteLocallyFreeOfRank r F.obj)
      (q : E ⟶ F) (h_q : Epi q.hom),
    IsEffectiveCartierDivisor (toScheme.map (projectiveBundleQuotient q h_q))

namespace Domain

variable {C : Type u} [Category.{v} C] {toScheme : C ⥤ Scheme.{w}}

/-- The actual class of O(P′) for the quotient divisor in Stacks 0FI4 (5). -/
def quotientDivisorClass (D : Domain toScheme) (X : C)
      (E F : ObjectProperty.FullSubcategory
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty (toScheme.obj X).Modules))
      (r : ℕ) (h_E : Scheme.Modules.IsFiniteLocallyFreeOfRank (r + 1) E.obj)
      (h_F : Scheme.Modules.IsFiniteLocallyFreeOfRank r F.obj)
      (q : E ⟶ F) (h_q : Epi q.hom) :
    (toScheme.obj (D.projectiveBundle X E)).PicardGroup :=
  WeilCohomology.effectiveCartierDivisorPicardClass
    (toScheme.map (D.projectiveBundleQuotient q h_q))
    (D.quotient_isEffectiveCartier X E F r h_E h_F q h_q)

end Domain

end AlgebraicGeometry.ChernClass
