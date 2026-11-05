/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import ReasLib.AlgebraicGeometry.ChernClass.Domain

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped BigOperators

noncomputable section

universe u v w x

namespace AlgebraicGeometry.ChernClass

/-- A graded cohomology theory on a geometric `Domain`, satisfying Stacks 0FI4 (1)--(5).
The `domain` field preserves the existing three-argument API. The other seven fields are
cohomological data and properties; the projective-bundle equivalence and O(P′) class are
computed, rather than supplied as redundant caches. -/
structure CohomologyTheory
    {C : Type u} [Category.{v} C] (toScheme : C ⥤ Scheme.{w})
    (A : Cᵒᵖ ⥤ RingCat.{x})
    (Agrade : ∀ X, ℕ → Submodule ℤ (A.obj (Opposite.op X)))
    [∀ X, GradedAlgebra (Agrade X)] where
  /-- The supplied category of schemes and its geometric closure data. -/
  domain : Domain toScheme
  /-- Pullback preserves every homogeneous degree. -/
  pullback_mem : ∀ {X' X : C} (f : X' ⟶ X) (i : ℕ) (a : Agrade X i),
    A.map f.op a ∈ Agrade X' i
  /-- Stacks 0FI4 (2): cohomology takes a decomposition into complementary clopen subschemes to a product. -/
  clopenProduct : ∀ (X : C) (U : (toScheme.obj X).Opens)
      (hU : IsClopen (U : Set (toScheme.obj X))),
    Function.Bijective fun a : A.obj (Opposite.op X) ↦
      (A.map (domain.clopenInclusion X U hU).op a,
        A.map (domain.clopenInclusion X (clopenComplement U hU) hU.compl).op a)
  /-- The additive first Chern class with values in degree one. -/
  firstChernClass : ∀ X, (toScheme.obj X).PicardGroup →+ Agrade X 1
  /-- Stacks 0FI4 (1): first Chern classes are central in the cohomology algebra. -/
  firstChernClass_central : ∀ (X : C) (L : (toScheme.obj X).PicardGroup)
      (a : A.obj (Opposite.op X)),
    (firstChernClass X L : A.obj (Opposite.op X)) * a =
      a * (firstChernClass X L : A.obj (Opposite.op X))
  /-- Stacks 0FI4 (3): first Chern classes commute with pullback. -/
  firstChernClass_naturality : ∀ {X' X : C} (f : X' ⟶ X)
      (L : (toScheme.obj X).PicardGroup),
    A.map f.op (firstChernClass X L : A.obj (Opposite.op X)) =
      (firstChernClass X'
        (Scheme.Hom.picardPullback (toScheme.map f) L) : A.obj (Opposite.op X'))
  /-- Stacks 0FI4 (4): the displayed projective-bundle map is bijective. -/
  projectiveBundleMap_bijective : ∀ (X : C)
      (E : ObjectProperty.FullSubcategory
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty (toScheme.obj X).Modules))
      (r : ℕ) (h_E : Scheme.Modules.IsFiniteLocallyFreeOfRank r E.obj),
    Function.Bijective fun a : Fin r → A.obj (Opposite.op X) ↦
      ∑ i : Fin r,
        (firstChernClass (domain.projectiveBundle X E)
          (tautologicalPicardClass
            (toScheme.map (domain.projectiveBundleProjection X E)) E.obj
            (domain.projectiveBundleRepresentation X E)) :
              A.obj (Opposite.op (domain.projectiveBundle X E))) ^ i.1 *
          A.map (domain.projectiveBundleProjection X E).op (a i)
  /-- Stacks 0FI4 (5): a class vanishing on the quotient divisor is annihilated by its first Chern class. -/
  cartierVanishing : ∀ (X : C)
      (E F : ObjectProperty.FullSubcategory
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty (toScheme.obj X).Modules))
      (r : ℕ) (h_E : Scheme.Modules.IsFiniteLocallyFreeOfRank (r + 1) E.obj)
      (h_F : Scheme.Modules.IsFiniteLocallyFreeOfRank r F.obj)
      (q : E ⟶ F) (h_q : Epi q.hom)
      (a : A.obj (Opposite.op (domain.projectiveBundle X E))),
    A.map (domain.projectiveBundleQuotient q h_q).op a = 0 →
      a * (firstChernClass (domain.projectiveBundle X E)
        (domain.quotientDivisorClass X E F r h_E h_F q h_q) :
          A.obj (Opposite.op (domain.projectiveBundle X E))) = 0

namespace CohomologyTheory

variable {C : Type u} [Category.{v} C] {toScheme : C ⥤ Scheme.{w}}
variable {A : Cᵒᵖ ⥤ RingCat.{x}}
    {Agrade : ∀ X, ℕ → Submodule ℤ (A.obj (Opposite.op X))}
    [∀ X, GradedAlgebra (Agrade X)]

/-- Compatibility projection to the geometric domain. -/
abbrev compactSpace (S : CohomologyTheory toScheme A Agrade) := @Domain.compactSpace _ _ toScheme S.domain

/-- Compatibility projection to the geometric domain. -/
abbrev quasiSeparatedSpace (S : CohomologyTheory toScheme A Agrade) := @Domain.quasiSeparatedSpace _ _ toScheme S.domain

/-- Compatibility projection to the geometric domain. -/
abbrev clopenObject (S : CohomologyTheory toScheme A Agrade) := @Domain.clopenObject _ _ toScheme S.domain

/-- Compatibility projection to the geometric domain. -/
abbrev clopenIso (S : CohomologyTheory toScheme A Agrade) := @Domain.clopenIso _ _ toScheme S.domain

/-- Compatibility projection to the geometric domain. -/
abbrev clopenInclusion (S : CohomologyTheory toScheme A Agrade) := @Domain.clopenInclusion _ _ toScheme S.domain

/-- Compatibility projection to the geometric domain. -/
abbrev clopenInclusion_map (S : CohomologyTheory toScheme A Agrade) := @Domain.clopenInclusion_map _ _ toScheme S.domain

/-- Compatibility projection to the geometric domain. -/
abbrev clopenFactor (S : CohomologyTheory toScheme A Agrade) := @Domain.clopenFactor _ _ toScheme S.domain

/-- Compatibility projection to the geometric domain. -/
abbrev clopenFactor_map (S : CohomologyTheory toScheme A Agrade) := @Domain.clopenFactor_map _ _ toScheme S.domain

/-- Compatibility projection to the geometric domain. -/
abbrev projectiveBundle (S : CohomologyTheory toScheme A Agrade) := @Domain.projectiveBundle _ _ toScheme S.domain

/-- Compatibility projection to the geometric domain. -/
abbrev projectiveBundleProjection (S : CohomologyTheory toScheme A Agrade) := @Domain.projectiveBundleProjection _ _ toScheme S.domain

/-- Compatibility projection to the geometric domain. -/
abbrev projectiveBundleRepresentation (S : CohomologyTheory toScheme A Agrade) := @Domain.projectiveBundleRepresentation _ _ toScheme S.domain

/-- Compatibility projection to the geometric domain. -/
abbrev projectiveBundlePullback (S : CohomologyTheory toScheme A Agrade) := @Domain.projectiveBundlePullback _ _ toScheme S.domain

/-- Compatibility projection to the geometric domain. -/
abbrev projectiveBundlePullback_map (S : CohomologyTheory toScheme A Agrade) := @Domain.projectiveBundlePullback_map _ _ toScheme S.domain

/-- Compatibility projection to the geometric domain. -/
abbrev projectiveBundlePullback_comm (S : CohomologyTheory toScheme A Agrade) := @Domain.projectiveBundlePullback_comm _ _ toScheme S.domain

/-- Compatibility projection to the geometric domain. -/
abbrev projectiveBundlePullback_isPullback (S : CohomologyTheory toScheme A Agrade) := @Domain.projectiveBundlePullback_isPullback _ _ toScheme S.domain

/-- Compatibility projection to the geometric domain. -/
abbrev projectiveBundleQuotient (S : CohomologyTheory toScheme A Agrade) := @Domain.projectiveBundleQuotient _ _ toScheme S.domain

/-- Compatibility projection to the geometric domain. -/
abbrev projectiveBundleQuotient_map (S : CohomologyTheory toScheme A Agrade) := @Domain.projectiveBundleQuotient_map _ _ toScheme S.domain

/-- Compatibility projection to the geometric domain. -/
abbrev projectiveBundleQuotient_isClosed (S : CohomologyTheory toScheme A Agrade) := @Domain.projectiveBundleQuotient_isClosed _ _ toScheme S.domain

/-- Compatibility projection to the geometric domain. -/
abbrev quotient_isEffectiveCartier (S : CohomologyTheory toScheme A Agrade) := @Domain.quotient_isEffectiveCartier _ _ toScheme S.domain

/-- Compatibility projection to the geometric domain. -/
abbrev quotientDivisorClass (S : CohomologyTheory toScheme A Agrade) := @Domain.quotientDivisorClass _ _ toScheme S.domain

/-- Internal grading follows from the supplied `GradedAlgebra`, without an extra axiom. -/
theorem grading_isInternal (S : CohomologyTheory toScheme A Agrade) (X : C) :
    DirectSum.IsInternal (Agrade X) :=
  DirectSum.Decomposition.isInternal (Agrade X)

/-- The equivalence derived from the explicit map and axiom 0FI4 (4). -/
def projectiveBundleEquiv (S : CohomologyTheory toScheme A Agrade) (X : C)
      (E : ObjectProperty.FullSubcategory
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty (toScheme.obj X).Modules))
      (r : ℕ) (h_E : Scheme.Modules.IsFiniteLocallyFreeOfRank r E.obj) :
    (Fin r → A.obj (Opposite.op X)) ≃
      A.obj (Opposite.op (S.projectiveBundle X E)) :=
  Equiv.ofBijective (fun a ↦
      ∑ i : Fin r,
        (S.firstChernClass (S.projectiveBundle X E)
          (tautologicalPicardClass
            (toScheme.map (S.projectiveBundleProjection X E)) E.obj
            (S.projectiveBundleRepresentation X E)) :
              A.obj (Opposite.op (S.projectiveBundle X E))) ^ i.1 *
          A.map (S.projectiveBundleProjection X E).op (a i)
    ) (S.projectiveBundleMap_bijective X E r h_E)

/-- The derived equivalence evaluates to the displayed sum. -/
theorem projectiveBundleEquiv_apply (S : CohomologyTheory toScheme A Agrade) (X : C)
      (E : ObjectProperty.FullSubcategory
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty (toScheme.obj X).Modules))
      (r : ℕ) (h_E : Scheme.Modules.IsFiniteLocallyFreeOfRank r E.obj)
      (a : Fin r → A.obj (Opposite.op X)) :
    S.projectiveBundleEquiv X E r h_E a =
      ∑ i : Fin r,
        (S.firstChernClass (S.projectiveBundle X E)
          (tautologicalPicardClass
            (toScheme.map (S.projectiveBundleProjection X E)) E.obj
            (S.projectiveBundleRepresentation X E)) :
              A.obj (Opposite.op (S.projectiveBundle X E))) ^ i.1 *
          A.map (S.projectiveBundleProjection X E).op (a i) := rfl

/-- The quotient class is the Picard class of the actual associated divisor sheaf. -/
theorem quotientDivisorClass_spec (S : CohomologyTheory toScheme A Agrade) (X : C)
      (E F : ObjectProperty.FullSubcategory
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty (toScheme.obj X).Modules))
      (r : ℕ) (h_E : Scheme.Modules.IsFiniteLocallyFreeOfRank (r + 1) E.obj)
      (h_F : Scheme.Modules.IsFiniteLocallyFreeOfRank r F.obj)
      (q : E ⟶ F) (h_q : Epi q.hom) :
    S.quotientDivisorClass X E F r h_E h_F q h_q =
      @Scheme.Modules.picardClass (toScheme.obj (S.projectiveBundle X E))
        (@Scheme.effectiveCartierDivisorAssociatedSheaf
          (toScheme.obj (S.projectiveBundle X E)) inferInstance
          (RingedSpace.Hom.idealSheafSubobject
            (toScheme.map (S.projectiveBundleQuotient q h_q)).toShHom)
          ⟨Scheme.Modules.Invertible.tensorRight_isEquivalence
            (S.quotient_isEffectiveCartier X E F r h_E h_F q h_q).invertibleIdealSheaf⟩)
        (@Scheme.effectiveCartierDivisorAssociatedSheaf_isInvertible
          (toScheme.obj (S.projectiveBundle X E)) inferInstance
          (RingedSpace.Hom.idealSheafSubobject
            (toScheme.map (S.projectiveBundleQuotient q h_q)).toShHom)
          ⟨Scheme.Modules.Invertible.tensorRight_isEquivalence
            (S.quotient_isEffectiveCartier X E F r h_E h_F q h_q).invertibleIdealSheaf⟩) := rfl

/-- The quotient-divisor class in a theory is canonically the Picard class of the associated
invertible sheaf of the effective Cartier divisor. -/
theorem quotientDivisorClass_eq
    {C : Type u} [Category.{v} C] {toScheme : C ⥤ Scheme.{w}}
    {A : Cᵒᵖ ⥤ RingCat.{x}}
    {Agrade : ∀ X, ℕ → Submodule ℤ (A.obj (Opposite.op X))}
    [∀ X, GradedAlgebra (Agrade X)] (S : CohomologyTheory toScheme A Agrade)
    (X : C)
    (E F : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty (toScheme.obj X).Modules))
    (r : ℕ) (h_E : Scheme.Modules.IsFiniteLocallyFreeOfRank (r + 1) E.obj)
    (h_F : Scheme.Modules.IsFiniteLocallyFreeOfRank r F.obj)
    (q : E ⟶ F) (h_q : Epi q.hom) :
    S.quotientDivisorClass X E F r h_E h_F q h_q =
      @Scheme.Modules.picardClass (toScheme.obj (S.projectiveBundle X E))
        (@Scheme.effectiveCartierDivisorAssociatedSheaf
          (toScheme.obj (S.projectiveBundle X E)) inferInstance
          (RingedSpace.Hom.idealSheafSubobject
            (toScheme.map (S.projectiveBundleQuotient q h_q)).toShHom)
          ⟨Scheme.Modules.Invertible.tensorRight_isEquivalence
            (S.quotient_isEffectiveCartier X E F r h_E h_F q h_q).invertibleIdealSheaf⟩)
        (@Scheme.effectiveCartierDivisorAssociatedSheaf_isInvertible
          (toScheme.obj (S.projectiveBundle X E)) inferInstance
          (RingedSpace.Hom.idealSheafSubobject
            (toScheme.map (S.projectiveBundleQuotient q h_q)).toShHom)
          ⟨Scheme.Modules.Invertible.tensorRight_isEquivalence
            (S.quotient_isEffectiveCartier X E F r h_E h_F q h_q).invertibleIdealSheaf⟩) := rfl

end CohomologyTheory

end AlgebraicGeometry.ChernClass
