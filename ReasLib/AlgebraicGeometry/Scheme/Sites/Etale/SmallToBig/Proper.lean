/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SmallToBig.Pushforward
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Etale.SmallToBig
open AlgebraicGeometry.Scheme.Hom
open CategoryTheory.Sheaf
open scoped MorphismOfTopoiIn

noncomputable section

universe w u

namespace AlgebraicGeometry.Scheme.Etale
namespace SmallToBig

variable {S T : Scheme.{u}} (f : T ⟶ S)

section Sets

variable [HasSheafify T.smallEtaleTopology (Type (u + 1))]
variable [HasSheafify S.smallEtaleTopology (Type (u + 1))]

/-- For a proper morphism `f : T ⟶ S` of schemes, the functors
`π_S⁻¹ ∘ f_small,*` and `f_big,* ∘ π_T⁻¹` from sheaves of sets on `T_étale` to sheaves
of sets on `(Sch/S)_étale` are canonically isomorphic via `smallBigPushforwardHom`. -/
theorem proper_smallBigPushforward_isIso [IsProper f] :
    IsIso (smallBigPushforwardHom f) := sorry

end Sets

section AbelianSheaves

variable [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}]
variable [HasSheafify (T.overGrothendieckTopology @Etale) AddCommGrpCat.{u}]
variable [∀ P : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
    (relocalizationFunctor (𝟙 S)).op.HasLeftKanExtension P]
variable [∀ P : T.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
    (relocalizationFunctor (𝟙 T)).op.HasLeftKanExtension P]
variable [∀ P : (Over T)ᵒᵖ ⥤ AddCommGrpCat.{u},
    (Over.map f).op.HasPointwiseRightKanExtension P]

/-- The abelian small-to-big mate is an isomorphism for a proper morphism. -/
theorem proper_abelianSmallBigPushforward_isIso [IsProper f] :
    IsIso (abelianSmallBigPushforwardHom f) := sorry

end AbelianSheaves

section Plus

variable [EnoughInjectives (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})]
variable [EnoughInjectives
    (Sheaf (T.overGrothendieckTopology @Etale) AddCommGrpCat.{u})]

variable [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}]
variable [HasSheafify (T.overGrothendieckTopology @Etale) AddCommGrpCat.{u}]
variable [∀ P : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
    (relocalizationFunctor (𝟙 S)).op.HasLeftKanExtension P]
variable [∀ P : T.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
    (relocalizationFunctor (𝟙 T)).op.HasLeftKanExtension P]
variable [∀ P : (Over T)ᵒᵖ ⥤ AddCommGrpCat.{u},
    (Over.map f).op.HasPointwiseRightKanExtension P]
variable [PreservesFiniteLimits (etalePiInverseImage S)]
variable [PreservesFiniteColimits (etalePiInverseImage S)]
variable [PreservesFiniteLimits (etalePiInverseImage T)]
variable [PreservesFiniteColimits (etalePiInverseImage T)]
variable [PreservesFiniteLimits (bigAbelianInverseImage f)]
variable [PreservesFiniteColimits (bigAbelianInverseImage f)]
variable [(abelianPushforwardAlong f).Additive]
variable [(bigAbelianPushforward f).Additive]
variable [HasDerivedCategory.{w} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory.{w} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory.{w}
    (Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u})]
variable [HasDerivedCategory.{w}
    (Sheaf (T.overGrothendieckTopology @Etale) AddCommGrpCat.{u})]
variable [(abelianPushforwardAlong f).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso (Sheaf T.smallEtaleTopology AddCommGrpCat.{u}))]
variable [(bigAbelianPushforward f).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (T.overGrothendieckTopology @Etale) AddCommGrpCat.{u}))]

/-- For a proper morphism `f : T ⟶ S` and `K` in `D⁺(T_étale)` whose
cohomology sheaves are locally torsion, the canonical mate
`π_S⁻¹ Rf_small,* K ⟶ Rf_big,* π_T⁻¹ K` is an isomorphism. -/
theorem proper_smallBigDerivedPushforward_plus_isIso [IsProper f]
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u}))
    (hK : DerivedCategory.Plus.cohomologyIn
      (IsLocallyTorsion :
        ObjectProperty (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})) K) :
    IsIso ((plusSmallBigPushforwardHom f).app K) := sorry

end Plus

section ZMod

/-- For a proper morphism `f : T ⟶ S`, `n ≥ 1`, and `K` in
`D(T_étale, ZMod n)`, the canonical mate `π_S⁻¹ Rf_small,* K ⟶ Rf_big,* π_T⁻¹ K`
is an isomorphism. -/
theorem proper_smallBigDerivedPushforward_zmod_isIso [IsProper f] (n : ℕ) [NeZero n]
    [HasSheafify (S.overGrothendieckTopology @Etale) (ModuleCat.{u} (ZMod n))]
    [HasSheafify (T.overGrothendieckTopology @Etale) (ModuleCat.{u} (ZMod n))]
    [HasDerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory
      (Sheaf (S.overGrothendieckTopology @Etale) (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory
      (Sheaf (T.overGrothendieckTopology @Etale) (ModuleCat.{u} (ZMod n)))]
    [IsGrothendieckAbelian
      (Sheaf (T.overGrothendieckTopology @Etale) (ModuleCat.{u} (ZMod n)))]
    [∀ P : S.Etaleᵒᵖ ⥤ ModuleCat.{u} (ZMod n),
      (relocalizationFunctor (𝟙 S)).op.HasLeftKanExtension P]
    [∀ P : T.Etaleᵒᵖ ⥤ ModuleCat.{u} (ZMod n),
      (relocalizationFunctor (𝟙 T)).op.HasLeftKanExtension P]
    [∀ P : (Over T)ᵒᵖ ⥤ ModuleCat.{u} (ZMod n),
      (Over.map f).op.HasPointwiseRightKanExtension P]
    [PreservesFiniteLimits (zmodPiInverseImage S n)]
    [PreservesFiniteColimits (zmodPiInverseImage S n)]
    [PreservesFiniteLimits (zmodPiInverseImage T n)]
    [PreservesFiniteColimits (zmodPiInverseImage T n)]
    [PreservesFiniteLimits (zmodBigInverseImage f n)]
    [PreservesFiniteColimits (zmodBigInverseImage f n)]
    [(zmodBigPushforward f n).Additive]
    [(zmodPiInverseImage S n).Additive]
    [(zmodPiInverseImage T n).Additive]
    [(zmodBigInverseImage f n).Additive]
    (K : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u} (ZMod n)))) :
    IsIso ((zmodSmallBigPushforwardHom f n).app K) := sorry

end ZMod

section Unbounded

variable [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}]
variable [HasSheafify (T.overGrothendieckTopology @Etale) AddCommGrpCat.{u}]
variable [∀ P : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
    (relocalizationFunctor (𝟙 S)).op.HasLeftKanExtension P]
variable [∀ P : T.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
    (relocalizationFunctor (𝟙 T)).op.HasLeftKanExtension P]
variable [∀ P : (Over T)ᵒᵖ ⥤ AddCommGrpCat.{u},
    (Over.map f).op.HasPointwiseRightKanExtension P]
variable [PreservesFiniteLimits (etalePiInverseImage S)]
variable [PreservesFiniteColimits (etalePiInverseImage S)]
variable [PreservesFiniteLimits (etalePiInverseImage T)]
variable [PreservesFiniteColimits (etalePiInverseImage T)]
variable [PreservesFiniteLimits (bigAbelianInverseImage f)]
variable [PreservesFiniteColimits (bigAbelianInverseImage f)]
variable [(abelianPushforwardAlong f).Additive]
variable [(bigAbelianPushforward f).Additive]
variable [HasDerivedCategory.{w} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory.{w} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory.{w}
    (Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u})]
variable [HasDerivedCategory.{w}
    (Sheaf (T.overGrothendieckTopology @Etale) AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian
    (Sheaf (T.overGrothendieckTopology @Etale) AddCommGrpCat.{u})]

/-- If `f : T ⟶ S` is finite, then for every `K` in `D(T_étale)` the
canonical mate `π_S⁻¹ Rf_small,* K ⟶ Rf_big,* π_T⁻¹ K` is an isomorphism. -/
theorem finite_smallBigDerivedPushforward_isIso [IsFinite f]
    (K : DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})) :
    IsIso ((unboundedSmallBigPushforwardHom f).app K) := sorry

end Unbounded

end SmallToBig
end AlgebraicGeometry.Scheme.Etale

end

end
