/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Ext.Resolution.Basic

@[expose] public section

/-!
# Fine-grained computation API for resolution Ext equivalences

The bundled `extAddEquiv` declarations are deliberately decomposed here into four canonical
transports: the derived shift comparison, the resolution quasi-isomorphism, the
homotopy-to-derived comparison, and the homotopy shift comparison.  Downstream code can use one
stage without unfolding the complete computation equivalence.
-/

open CategoryTheory ComplexShape DerivedCategory HomotopyCategory
open scoped DerivedExt

noncomputable section

universe w v u

namespace CochainComplex

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

local notation "KQ" => HomotopyCategory.quotient 𝒜 (up ℤ)

namespace IsKInjective

/-- The additive homotopy-to-derived equivalence for a K-injective target.  This is the
resolution-independent owner; the injective-resolution specialization below uses its inverse. -/
@[stacks 070I]
noncomputable def homAddEquiv
    (M : HomotopyCategory 𝒜 (up ℤ)) (I : CochainComplex 𝒜 ℤ) [I.IsKInjective] :
    (M ⟶ (KQ).obj I) ≃+
      (DerivedCategory.Qh.obj M ⟶ DerivedCategory.Qh.obj ((KQ).obj I)) :=
  AddEquiv.ofBijective
    (DerivedCategory.Qh.mapAddHom :
      (M ⟶ (KQ).obj I) →+ (DerivedCategory.Qh.obj M ⟶ DerivedCategory.Qh.obj ((KQ).obj I)))
    (CochainComplex.IsKInjective.Qh_map_bijective M I)

/-- Evaluation of the K-injective additive Hom equivalence is the canonical `Qh` map. -/
@[simp, stacks 070I]
theorem homAddEquiv_apply
    (M : HomotopyCategory 𝒜 (up ℤ)) (I : CochainComplex 𝒜 ℤ) [I.IsKInjective]
    (f : M ⟶ (KQ).obj I) :
    homAddEquiv M I f = DerivedCategory.Qh.map f := sorry

/-- The K-injective Hom equivalence is contravariantly natural in its homotopy source. -/
@[reassoc, stacks 070I]
theorem homAddEquiv_naturality_left
    {M M' : HomotopyCategory 𝒜 (up ℤ)} (I : CochainComplex 𝒜 ℤ) [I.IsKInjective]
    (f : M' ⟶ M) (g : M ⟶ (KQ).obj I) :
    homAddEquiv M' I (f ≫ g) = DerivedCategory.Qh.map f ≫ homAddEquiv M I g := sorry

/-- The K-injective Hom equivalence is covariantly natural in a map between K-injective targets. -/
@[reassoc, stacks 070I]
theorem homAddEquiv_naturality_right
    (M : HomotopyCategory 𝒜 (up ℤ)) (I J : CochainComplex 𝒜 ℤ)
    [I.IsKInjective] [J.IsKInjective]
    (f : M ⟶ (KQ).obj I) (g : (KQ).obj I ⟶ (KQ).obj J) :
    homAddEquiv M J (f ≫ g) = homAddEquiv M I f ≫ DerivedCategory.Qh.map g := sorry

end IsKInjective

namespace IsKProjective

/-- The additive homotopy-to-derived equivalence for a K-projective source. -/
@[stacks 064B]
noncomputable def homAddEquiv
    (P : CochainComplex 𝒜 ℤ) (K : HomotopyCategory 𝒜 (up ℤ)) [P.IsKProjective] :
    ((KQ).obj P ⟶ K) ≃+
      (DerivedCategory.Qh.obj ((KQ).obj P) ⟶ DerivedCategory.Qh.obj K) :=
  AddEquiv.ofBijective
    (DerivedCategory.Qh.mapAddHom :
      ((KQ).obj P ⟶ K) →+ (DerivedCategory.Qh.obj ((KQ).obj P) ⟶ DerivedCategory.Qh.obj K))
    (CochainComplex.IsKProjective.Qh_map_bijective P K)

/-- Evaluation of the K-projective additive Hom equivalence is the canonical `Qh` map. -/
@[simp, stacks 064B]
theorem homAddEquiv_apply
    (P : CochainComplex 𝒜 ℤ) (K : HomotopyCategory 𝒜 (up ℤ)) [P.IsKProjective]
    (f : (KQ).obj P ⟶ K) :
    homAddEquiv P K f = DerivedCategory.Qh.map f := sorry

/-- The K-projective Hom equivalence is contravariantly natural in a map between projective
sources. -/
@[reassoc, stacks 064B]
theorem homAddEquiv_naturality_left
    (P P' : CochainComplex 𝒜 ℤ) (K : HomotopyCategory 𝒜 (up ℤ))
    [P.IsKProjective] [P'.IsKProjective]
    (f : (KQ).obj P ⟶ (KQ).obj P') (g : (KQ).obj P' ⟶ K) :
    homAddEquiv P K (f ≫ g) = DerivedCategory.Qh.map f ≫ homAddEquiv P' K g := sorry

/-- The K-projective Hom equivalence is covariantly natural in its homotopy target. -/
@[reassoc, stacks 064B]
theorem homAddEquiv_naturality_right
    (P : CochainComplex 𝒜 ℤ) {K K' : HomotopyCategory 𝒜 (up ℤ)} [P.IsKProjective]
    (f : (KQ).obj P ⟶ K) (g : K ⟶ K') :
    homAddEquiv P K' (f ≫ g) = homAddEquiv P K f ≫ DerivedCategory.Qh.map g := sorry

end IsKProjective

namespace Resolution

/-- The additive comparison between a shifted derived Hom and a Hom into a shifted complex. -/
@[stacks 06XR]
noncomputable def shiftAddEquiv (X Y : CochainComplex 𝒜 ℤ) (i : ℤ) :
    Ext⁽i⁾(Q.obj X, Q.obj Y) ≃+ (Q.obj X ⟶ Q.obj (Y⟦i⟧)) :=
  Iso.homCongrAddEquiv (Iso.refl _) ((Q.commShiftIso i).app Y).symm

/-- Evaluation of the derived shift comparison is postcomposition with the inverse comparison. -/
@[simp, stacks 06XR]
theorem shiftAddEquiv_apply (X Y : CochainComplex 𝒜 ℤ) (i : ℤ)
    (f : Ext⁽i⁾(Q.obj X, Q.obj Y)) :
    shiftAddEquiv X Y i f = f ≫ (Q.commShiftIso i).inv.app Y := sorry

/-- The inverse derived shift comparison postcomposes with the forward comparison. -/
@[simp, stacks 06XR]
theorem shiftAddEquiv_symm_apply (X Y : CochainComplex 𝒜 ℤ) (i : ℤ)
    (f : Q.obj X ⟶ Q.obj (Y⟦i⟧)) :
    (shiftAddEquiv X Y i).symm f = f ≫ (Q.commShiftIso i).hom.app Y := sorry

/-- The additive comparison between a Hom into a shifted homotopy complex and a shifted Hom. -/
@[stacks 06XR]
noncomputable def shiftedHomAddEquiv (X Y : CochainComplex 𝒜 ℤ) (i : ℤ) :
    ((KQ).obj X ⟶ (KQ).obj (Y⟦i⟧)) ≃+
      Ext⁽i⁾((KQ).obj X, (KQ).obj Y) :=
  Iso.homCongrAddEquiv (Iso.refl _)
    (((HomotopyCategory.quotient 𝒜 (up ℤ)).commShiftIso i).app Y)

/-- Evaluation of the homotopy shift comparison is postcomposition with its forward map. -/
@[simp, stacks 06XR]
theorem shiftedHomAddEquiv_apply (X Y : CochainComplex 𝒜 ℤ) (i : ℤ)
    (f : (KQ).obj X ⟶ (KQ).obj (Y⟦i⟧)) :
    shiftedHomAddEquiv X Y i f =
      f ≫ ((HomotopyCategory.quotient 𝒜 (up ℤ)).commShiftIso i).hom.app Y := sorry

/-- The inverse homotopy shift comparison postcomposes with its inverse map. -/
@[simp, stacks 06XR]
theorem shiftedHomAddEquiv_symm_apply (X Y : CochainComplex 𝒜 ℤ) (i : ℤ)
    (f : Ext⁽i⁾((KQ).obj X, (KQ).obj Y)) :
    (shiftedHomAddEquiv X Y i).symm f =
      f ≫ ((HomotopyCategory.quotient 𝒜 (up ℤ)).commShiftIso i).inv.app Y := sorry

end Resolution

namespace InjectiveResolution

variable {Y : CochainComplex 𝒜 ℤ}

/-- Transport the target of a shifted morphism along the resolution quasi-isomorphism. -/
@[stacks 06XR]
noncomputable def resolutionAddEquiv (I : InjectiveResolution Y) (X : CochainComplex 𝒜 ℤ)
    (i : ℤ) :
    (Q.obj X ⟶ Q.obj (Y⟦i⟧)) ≃+ (Q.obj X ⟶ Q.obj (I⟦i⟧)) :=
  Iso.homCongrAddEquiv (Iso.refl _) (shiftedComparisonIso I i)

/-- Evaluation of `resolutionAddEquiv` is postcomposition with the shifted comparison map. -/
@[simp, stacks 06XR]
theorem resolutionAddEquiv_apply (I : InjectiveResolution Y) (X : CochainComplex 𝒜 ℤ) (i : ℤ)
    (f : Q.obj X ⟶ Q.obj (Y⟦i⟧)) :
    resolutionAddEquiv I X i f = f ≫ Q.map (I.ι⟦i⟧') := sorry

/-- The inverse target transport postcomposes with the inverse shifted comparison. -/
@[simp, stacks 06XR]
theorem resolutionAddEquiv_symm_apply (I : InjectiveResolution Y) (X : CochainComplex 𝒜 ℤ)
    (i : ℤ) (f : Q.obj X ⟶ Q.obj (I⟦i⟧)) :
    (resolutionAddEquiv I X i).symm f = f ≫ (shiftedComparisonIso I i).inv := sorry

/-- The additive homotopy-to-derived comparison equivalence for a shifted injective resolution. -/
@[stacks 06XR]
noncomputable def homotopyAddEquiv (I : InjectiveResolution Y) (X : CochainComplex 𝒜 ℤ)
    (i : ℤ) :
    (Q.obj X ⟶ Q.obj (I⟦i⟧)) ≃+ ((KQ).obj X ⟶ (KQ).obj (I⟦i⟧)) :=
  (AddEquiv.ofBijective
      (Qh.mapAddHom : ((KQ).obj X ⟶ (KQ).obj (I⟦i⟧)) →+ _)
      (IsKInjective.Qh_map_bijective ((KQ).obj X) (I⟦i⟧))).symm

/-- Evaluation of `homotopyAddEquiv` is the inverse of the additive `Qh.map` equivalence. -/
@[simp, stacks 06XR]
theorem homotopyAddEquiv_apply (I : InjectiveResolution Y) (X : CochainComplex 𝒜 ℤ) (i : ℤ)
    (f : Q.obj X ⟶ Q.obj (I⟦i⟧)) :
    Qh.map (homotopyAddEquiv I X i f) = f := sorry

/-- The inverse homotopy transport is characterized by mapping to the supplied derived morphism. -/
@[simp, stacks 06XR]
theorem homotopyAddEquiv_symm_apply (I : InjectiveResolution Y) (X : CochainComplex 𝒜 ℤ) (i : ℤ)
    (f : (KQ).obj X ⟶ (KQ).obj (I⟦i⟧)) :
    (homotopyAddEquiv I X i).symm f = Qh.map f := sorry

/-- The bundled resolution computation is the composite of the four named transports. -/
@[stacks 06XR]
theorem extAddEquiv_eq (I : InjectiveResolution Y) (X : CochainComplex 𝒜 ℤ) (i : ℤ) :
    I.extAddEquiv X i =
      (Resolution.shiftAddEquiv X Y i).trans
        ((resolutionAddEquiv I X i).trans
          ((homotopyAddEquiv I X i).trans (Resolution.shiftedHomAddEquiv X I i))) := sorry

/-- Pointwise computation of the injective-resolution equivalence through its named stages. -/
@[stacks 06XR]
theorem extAddEquiv_apply (I : InjectiveResolution Y) (X : CochainComplex 𝒜 ℤ) (i : ℤ)
    (f : Ext⁽i⁾(Q.obj X, Q.obj Y)) :
    I.extAddEquiv X i f =
      Resolution.shiftedHomAddEquiv X I i
        (homotopyAddEquiv I X i
          (resolutionAddEquiv I X i (Resolution.shiftAddEquiv X Y i f))) := sorry

/-- Inverse computation for the injective-resolution equivalence through the four named stages. -/
@[stacks 06XR]
theorem extAddEquiv_symm_apply (I : InjectiveResolution Y) (X : CochainComplex 𝒜 ℤ) (i : ℤ)
    (f : Ext⁽i⁾((KQ).obj X, (KQ).obj I)) :
    (I.extAddEquiv X i).symm f =
      (Resolution.shiftAddEquiv X Y i).symm
        ((resolutionAddEquiv I X i).symm
          ((homotopyAddEquiv I X i).symm
            ((Resolution.shiftedHomAddEquiv X I i).symm f))) := sorry

end InjectiveResolution

namespace ProjectiveResolution

variable {X : CochainComplex 𝒜 ℤ}

/-- Transport the source of a shifted morphism along the projective resolution quasi-isomorphism. -/
@[stacks 06XR]
noncomputable def resolutionAddEquiv (P : ProjectiveResolution X) (Y : CochainComplex 𝒜 ℤ)
    (i : ℤ) :
    (Q.obj X ⟶ Q.obj (Y⟦i⟧)) ≃+ (Q.obj P ⟶ Q.obj (Y⟦i⟧)) :=
  Iso.homCongrAddEquiv (comparisonIso P).symm (Iso.refl _)

/-- Evaluation of `resolutionAddEquiv` is precomposition with the inverse localized comparison. -/
@[simp, stacks 06XR]
theorem resolutionAddEquiv_apply (P : ProjectiveResolution X) (Y : CochainComplex 𝒜 ℤ) (i : ℤ)
    (f : Q.obj X ⟶ Q.obj (Y⟦i⟧)) :
    resolutionAddEquiv P Y i f = (comparisonIso P).hom ≫ f := sorry

/-- The inverse source transport precomposes with the forward localized comparison. -/
@[simp, stacks 06XR]
theorem resolutionAddEquiv_symm_apply (P : ProjectiveResolution X) (Y : CochainComplex 𝒜 ℤ)
    (i : ℤ) (f : Q.obj P ⟶ Q.obj (Y⟦i⟧)) :
    (resolutionAddEquiv P Y i).symm f = (comparisonIso P).inv ≫ f := sorry

/-- The additive homotopy-to-derived comparison equivalence for a shifted projective resolution. -/
@[stacks 06XR]
noncomputable def homotopyAddEquiv (P : ProjectiveResolution X) (Y : CochainComplex 𝒜 ℤ)
    (i : ℤ) :
    (Q.obj P ⟶ Q.obj (Y⟦i⟧)) ≃+ ((KQ).obj P ⟶ (KQ).obj (Y⟦i⟧)) :=
  (AddEquiv.ofBijective
      (Qh.mapAddHom : ((KQ).obj P ⟶ (KQ).obj (Y⟦i⟧)) →+ _)
      (IsKProjective.Qh_map_bijective (P : CochainComplex 𝒜 ℤ)
        ((KQ).obj (Y⟦i⟧)))).symm

/-- Evaluation of `homotopyAddEquiv` is characterized by the `Qh` map. -/
@[simp, stacks 06XR]
theorem homotopyAddEquiv_apply (P : ProjectiveResolution X) (Y : CochainComplex 𝒜 ℤ) (i : ℤ)
    (f : Q.obj (P : CochainComplex 𝒜 ℤ) ⟶ Q.obj (Y⟦i⟧)) :
    Qh.map (homotopyAddEquiv P Y i f) = f := sorry

/-- The inverse projective homotopy transport is characterized by mapping to the supplied derived
morphism. -/
@[simp, stacks 06XR]
theorem homotopyAddEquiv_symm_apply (P : ProjectiveResolution X) (Y : CochainComplex 𝒜 ℤ)
    (i : ℤ) (f : (KQ).obj P ⟶ (KQ).obj (Y⟦i⟧)) :
    (homotopyAddEquiv P Y i).symm f = Qh.map f := sorry

/-- The bundled projective computation is the composite of the four named transports. -/
@[stacks 06XR]
theorem extAddEquiv_eq (P : ProjectiveResolution X) (Y : CochainComplex 𝒜 ℤ) (i : ℤ) :
    P.extAddEquiv Y i =
      (Resolution.shiftAddEquiv X Y i).trans
        ((resolutionAddEquiv P Y i).trans
          ((homotopyAddEquiv P Y i).trans (Resolution.shiftedHomAddEquiv P Y i))) := sorry

/-- Pointwise computation of the projective-resolution equivalence through its named stages. -/
@[stacks 06XR]
theorem extAddEquiv_apply (P : ProjectiveResolution X) (Y : CochainComplex 𝒜 ℤ) (i : ℤ)
    (f : Ext⁽i⁾(Q.obj X, Q.obj Y)) :
    P.extAddEquiv Y i f =
      Resolution.shiftedHomAddEquiv P Y i
        (homotopyAddEquiv P Y i
          (resolutionAddEquiv P Y i (Resolution.shiftAddEquiv X Y i f))) := sorry

/-- Inverse computation for the projective-resolution equivalence through the four named stages. -/
@[stacks 06XR]
theorem extAddEquiv_symm_apply (P : ProjectiveResolution X) (Y : CochainComplex 𝒜 ℤ) (i : ℤ)
    (f : Ext⁽i⁾((KQ).obj P, (KQ).obj Y)) :
    (P.extAddEquiv Y i).symm f =
      (Resolution.shiftAddEquiv X Y i).symm
        ((resolutionAddEquiv P Y i).symm
          ((homotopyAddEquiv P Y i).symm
            ((Resolution.shiftedHomAddEquiv P Y i).symm f))) := sorry

end ProjectiveResolution

end

end CochainComplex
