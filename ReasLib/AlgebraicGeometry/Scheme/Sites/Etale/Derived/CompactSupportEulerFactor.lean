/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.Determinant.EulerFactor
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.CompactSupportTrace
public import ReasLib.AlgebraicGeometry.Scheme.AffineStratification
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.Nagata
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero.Exactness
public import Mathlib.AlgebraicGeometry.Noetherian

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.SchemeOverField
open CategoryTheory.DerivedCategory CategoryTheory.MonoidalCategory Opposite ComplexShape
open scoped AlgebraicGeometry MonoidalCategory

universe u

noncomputable section

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k] [Fintype k]
variable {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
variable {Λ : Type u} [CommRing Λ] [Finite Λ] [IsNoetherianRing Λ]
variable [HasColimitsOfSize.{u, u} (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}}, HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}} (U : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}},
    HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
    (smallEtalePullback f).op.HasLeftKanExtension F]
variable [∀ {Y : Scheme.{u}},
    ((sheafSections Y.smallEtaleTopology (ModuleCat.{u} Λ)).obj
      (op (Etale.globalEtale Y))).Additive]
variable [∀ {Y : Scheme.{u}},
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((sheafSections Y.smallEtaleTopology (ModuleCat.{u} Λ)).obj
          (op (Etale.globalEtale Y))))
      (HomologicalComplex.quasiIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (up ℤ))]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    ((smallEtalePullback f).sheafPullback (ModuleCat.{u} Λ)
      Y.smallEtaleTopology X.smallEtaleTopology).Additive]
variable [∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    PreservesFiniteLimits
      ((smallEtalePullback f).sheafPullback (ModuleCat.{u} Λ)
        Y.smallEtaleTopology X.smallEtaleTopology)]
variable [∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    PreservesFiniteColimits
      ((smallEtalePullback f).sheafPullback (ModuleCat.{u} Λ)
        Y.smallEtaleTopology X.smallEtaleTopology)]
variable [∀ {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B),
    (((smallEtalePullback p).sheafPullback (ModuleCat.{u} Λ)
        A.smallEtaleTopology B.smallEtaleTopology) ⋙
      ((smallEtalePullback q).sheafPullback (ModuleCat.{u} Λ)
        B.smallEtaleTopology C.smallEtaleTopology)).Additive]
variable [∀ {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B),
    PreservesFiniteLimits
      (((smallEtalePullback p).sheafPullback (ModuleCat.{u} Λ)
          A.smallEtaleTopology B.smallEtaleTopology) ⋙
        ((smallEtalePullback q).sheafPullback (ModuleCat.{u} Λ)
          B.smallEtaleTopology C.smallEtaleTopology))]
variable [∀ {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B),
    PreservesFiniteColimits
      (((smallEtalePullback p).sheafPullback (ModuleCat.{u} Λ)
          A.smallEtaleTopology B.smallEtaleTopology) ⋙
        ((smallEtalePullback q).sheafPullback (ModuleCat.{u} Λ)
          B.smallEtaleTopology C.smallEtaleTopology))]
variable [∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).Additive]
variable [∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    PreservesFiniteLimits (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ))]
variable [∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    PreservesFiniteColimits (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ))]
variable [∀ {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B),
    (Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ) ⋙
      Sheaf.smallEtaleInverseImage q (ModuleCat.{u} Λ)).Additive]
variable [∀ {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B),
    PreservesFiniteLimits
      (Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ) ⋙
        Sheaf.smallEtaleInverseImage q (ModuleCat.{u} Λ))]
variable [∀ {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B),
    PreservesFiniteColimits
      (Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ) ⋙
        Sheaf.smallEtaleInverseImage q (ModuleCat.{u} Λ))]
variable [∀ {Y : Scheme.{u}},
    (Y.smallEtaleTopology.W (A := ModuleCat.{u} Λ)).IsMonoidal]

/-- Compactly supported geometric derived sections of a constructible flat sheaf with
finite coefficients of order invertible in the base field are perfect. -/
theorem isPerfect_geometricRGammaCompactSupport_of_constructibleFlat
    (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom]
    (P : Compactification.Of (Spec (CommRingCat.of k)) X)
    (hΛ : Nat.Coprime (Nat.card Λ) p)
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (hF : Sheaf.IsConstructibleEtaleModule
      (fun {Y} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
      (fun {Y} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
    [IsFlat F] :
    DerivedCategory.IsPerfect
      (geometricRGammaCompactSupport X P
        ((DerivedCategory.singleFunctor
          (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (0 : ℤ)).obj F)) := sorry

/-- The inverse determinant of compact-support geometric Frobenius is independent of the
compactification. -/
theorem eulerFactor_geometricFrobeniusCompactSupport_independent
    (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom]
    (P Q : Compactification.Of (Spec (CommRingCat.of k)) X)
    (hΛ : Nat.Coprime (Nat.card Λ) p)
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (hF : Sheaf.IsConstructibleEtaleModule
      (fun {Y} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
      (fun {Y} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
    [IsFlat F] :
    (isPerfect_geometricRGammaCompactSupport_of_constructibleFlat X P hΛ F hF).eulerFactor
      (geometricFrobeniusRGammaCompactSupport X P
        ((DerivedCategory.singleFunctor
          (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (0 : ℤ)).obj F)) 1 =
    (isPerfect_geometricRGammaCompactSupport_of_constructibleFlat X Q hΛ F hF).eulerFactor
      (geometricFrobeniusRGammaCompactSupport X Q
        ((DerivedCategory.singleFunctor
          (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (0 : ℤ)).obj F)) 1 := sorry

namespace CompactSupport

/-- The reduced scheme of a locally closed affine stratum, with its induced map to the
base field. -/
def stratum (X : SchemeOverField k) (S : FiniteAffineStratification.{u, 0} X.left)
    (i : S.index) : SchemeOverField k :=
  Over.mk (LocallyClosedReduction.ι
    ⟨S.strata i, @IsStratification.locallyClosed X.left _ S.index S.instPartialOrder
      S.strata S.isStratification i⟩ ≫ X.hom)

/-- The canonical immersion of a reduced affine stratum into its ambient scheme. -/
def stratumι (X : SchemeOverField k) (S : FiniteAffineStratification.{u, 0} X.left)
    (i : S.index) : (stratum X S i).left ⟶ X.left :=
  LocallyClosedReduction.ι
    ⟨S.strata i, @IsStratification.locallyClosed X.left _ S.index S.instPartialOrder
      S.strata S.isStratification i⟩

/-- The inverse-image coefficient sheaf on a reduced affine stratum. -/
def stratumSheaf (X : SchemeOverField k) (S : FiniteAffineStratification.{u, 0} X.left)
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (i : S.index) :
    Sheaf (stratum X S i).left.smallEtaleTopology (ModuleCat.{u} Λ) :=
  (Sheaf.smallEtaleInverseImage (stratumι X S i) (ModuleCat.{u} Λ)).obj F

/-- Compactly supported geometric derived sections of the restriction of a constructible
flat sheaf to a reduced affine stratum are perfect. -/
theorem isPerfect_stratumRGammaCompactSupport
    (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom]
    (S : FiniteAffineStratification.{u, 0} X.left) (i : S.index)
    (P : Compactification.Of (Spec (CommRingCat.of k)) (stratum X S i))
    (hΛ : Nat.Coprime (Nat.card Λ) p)
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (hF : Sheaf.IsConstructibleEtaleModule
      (fun {Y} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
      (fun {Y} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
    [IsFlat F] :
    DerivedCategory.IsPerfect
      (geometricRGammaCompactSupport (stratum X S i) P
        ((DerivedCategory.singleFunctor
          (Sheaf (stratum X S i).left.smallEtaleTopology (ModuleCat.{u} Λ)) (0 : ℤ)).obj (stratumSheaf X S F i))) := sorry

/-- The product of compact-support Frobenius inverse determinants over the reduced affine
strata, with an explicit compactification of each stratum. -/
def stratifiedEulerFactor
    (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom]
    (S : FiniteAffineStratification.{u, 0} X.left)
    (P : ∀ i : S.index, Compactification.Of (Spec (CommRingCat.of k)) (stratum X S i))
    (hΛ : Nat.Coprime (Nat.card Λ) p)
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (hF : Sheaf.IsConstructibleEtaleModule
      (fun {Y} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
      (fun {Y} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
    [IsFlat F] : PowerSeries Λ :=
  (@Finset.univ S.index (@Fintype.ofFinite S.index S.instFinite)).prod fun i ↦
    (isPerfect_stratumRGammaCompactSupport X S i (P i) hΛ F hF).eulerFactor
      (geometricFrobeniusRGammaCompactSupport (stratum X S i) (P i)
        ((DerivedCategory.singleFunctor
          (Sheaf (stratum X S i).left.smallEtaleTopology (ModuleCat.{u} Λ)) (0 : ℤ)).obj (stratumSheaf X S F i))) 1

/-- Products of compact-support Frobenius inverse determinants agree for all finite affine
stratifications and all compactifications of their strata. -/
theorem stratifiedEulerFactor_independent
    (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom]
    (S T : FiniteAffineStratification.{u, 0} X.left)
    (P : ∀ i : S.index, Compactification.Of (Spec (CommRingCat.of k)) (stratum X S i))
    (Q : ∀ i : T.index, Compactification.Of (Spec (CommRingCat.of k)) (stratum X T i))
    (hΛ : Nat.Coprime (Nat.card Λ) p)
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (hF : Sheaf.IsConstructibleEtaleModule
      (fun {Y} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
      (fun {Y} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
    [IsFlat F] :
    stratifiedEulerFactor X S P hΛ F hF = stratifiedEulerFactor X T Q hΛ F hF := sorry

/-- The compact-support geometric Frobenius inverse determinant, extended to finite-type
schemes by the finite product over a chosen reduced affine stratification. -/
def eulerFactor
    (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom]
    (hΛ : Nat.Coprime (Nat.card Λ) p)
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (hF : Sheaf.IsConstructibleEtaleModule
      (fun {Y} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
      (fun {Y} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
    [IsFlat F] : PowerSeries Λ :=
  let S := Classical.choice
    ((FiniteAffineStratification.nonempty_iff_compactSpace_and_quasiSeparatedSpace X.left).mpr
      ⟨QuasiCompact.compactSpace_of_compactSpace X.hom,
        @IsLocallyNoetherian.quasiSeparatedSpace X.left
          (LocallyOfFiniteType.isLocallyNoetherian X.hom)⟩)
  let P : ∀ i : S.index,
      Compactification.Of (Spec (CommRingCat.of k)) (stratum X S i) := fun i ↦
    -- Local instance justification (noncanonical choice): the chosen stratification stores the affine proof for its stratum, so inference must be supplied this proof at the point of compactification.
    letI : IsAffine (stratum X S i).left := S.stratum_isAffine i
    -- Local instance justification (proof-local temporary data): Nagata compactification needs the finite-type proof for this chosen stratum; its immersion composite supplies local finite type and its affineness supplies quasi-compactness.
    letI : Scheme.Hom.FiniteType (stratum X S i).hom :=
      { toQuasiCompact := inferInstance
        toLocallyOfFiniteType := inferInstanceAs
          (LocallyOfFiniteType (LocallyClosedReduction.ι
            ⟨S.strata i, @IsStratification.locallyClosed X.left _ S.index S.instPartialOrder
              S.strata S.isStratification i⟩ ≫ X.hom)) }
    Classical.choice (Compactification.Of.nonempty_of_finiteType (stratum X S i).hom)
  stratifiedEulerFactor X S P hΛ F hF

/-- The compact-support inverse determinant is computed using any finite affine
stratification and any family of compactifications of its strata. -/
theorem eulerFactor_spec
    (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom]
    (S : FiniteAffineStratification.{u, 0} X.left)
    (P : ∀ i : S.index, Compactification.Of (Spec (CommRingCat.of k)) (stratum X S i))
    (hΛ : Nat.Coprime (Nat.card Λ) p)
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (hF : Sheaf.IsConstructibleEtaleModule
      (fun {Y} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
      (fun {Y} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
    [IsFlat F] :
    eulerFactor X hΛ F hF = stratifiedEulerFactor X S P hΛ F hF := sorry

/-- On a compactifiable scheme, the stratification-defined inverse determinant agrees
with the determinant on its compactly supported geometric derived sections. -/
theorem eulerFactor_eq_compactification
    (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom]
    (P : Compactification.Of (Spec (CommRingCat.of k)) X)
    (hΛ : Nat.Coprime (Nat.card Λ) p)
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (hF : Sheaf.IsConstructibleEtaleModule
      (fun {Y} f ↦ (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj)
      (fun {Y} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
    [IsFlat F] :
    eulerFactor X hΛ F hF =
      (isPerfect_geometricRGammaCompactSupport_of_constructibleFlat X P hΛ F hF).eulerFactor
        (geometricFrobeniusRGammaCompactSupport X P
          ((DerivedCategory.singleFunctor
          (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (0 : ℤ)).obj F)) 1 := sorry

end CompactSupport

end AlgebraicGeometry.SchemeOverField
