/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Over.StalkGluing
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Over.Concrete
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Cancellation
public import ReasLib.AlgebraicGeometry.Scheme.Limit.Separated
public import ReasLib.AlgebraicGeometry.Scheme.Limit.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Limit.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Limit.Etale

/-!
# Properties of finite-presentation stalk gluing near a point

This file records that standard properties of the open and stalk components of finite-presentation
gluing data hold on a sufficiently small open neighborhood of the gluing point.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.FinitePresentationOver.StalkGluing

/-- If the open and stalk components of a finite-presentation gluing object are separated, then
the object is separated over some smaller open neighborhood containing the fixed open. -/
theorem existsOpenNeighborhood_isSeparated_of_object_components
    (S : Scheme.{u}) (U U' : S.Opens) [QuasiCompact U.ι]
    (s : S) (hsU : s ∉ (U : Set S)) (hUU' : U ≤ U') (hsU' : s ∈ (U' : Set S))
    (X' : FinitePresentationOver U'.toScheme)
    (G : finitePresentationStalkGluingCategory S U s)
    (hOpenIso : Nonempty (FinitePresentationOver.restrictOverObject hUU' X' ≅ G.fst.obj))
    (hStalkIso : Nonempty
      (FinitePresentationOver.baseChangeOverObject (U'.fromSpecStalkOfMem s hsU') X' ≅
        G.snd.obj))
    (hopen : IsSeparated (Comma.hom G.fst.obj))
    (hstalk : IsSeparated (Comma.hom G.snd.obj)) :
    ∃ (W : S.Opens) (hUW : U ≤ W) (hWU' : W ≤ U'),
      s ∈ (W : Set S) ∧
        IsSeparated (FinitePresentationOver.restrictOverObject hWU' X').hom := sorry

/-- If the open and stalk components of a finite-presentation gluing object are proper, then
the object is proper over some smaller open neighborhood containing the fixed open. -/
theorem existsOpenNeighborhood_isProper_of_object_components
    (S : Scheme.{u}) (U U' : S.Opens) [QuasiCompact U.ι]
    (s : S) (hsU : s ∉ (U : Set S)) (hUU' : U ≤ U') (hsU' : s ∈ (U' : Set S))
    (X' : FinitePresentationOver U'.toScheme)
    (G : finitePresentationStalkGluingCategory S U s)
    (hOpenIso : Nonempty (FinitePresentationOver.restrictOverObject hUU' X' ≅ G.fst.obj))
    (hStalkIso : Nonempty
      (FinitePresentationOver.baseChangeOverObject (U'.fromSpecStalkOfMem s hsU') X' ≅
        G.snd.obj))
    (hopen : IsProper (Comma.hom G.fst.obj))
    (hstalk : IsProper (Comma.hom G.snd.obj)) :
    ∃ (W : S.Opens) (hUW : U ≤ W) (hWU' : W ≤ U'),
      s ∈ (W : Set S) ∧
        IsProper (FinitePresentationOver.restrictOverObject hWU' X').hom := sorry

/-- If the open and stalk components of a finite-presentation gluing object are finite, then
the object is finite over some smaller open neighborhood containing the fixed open. -/
theorem existsOpenNeighborhood_isFinite_of_object_components
    (S : Scheme.{u}) (U U' : S.Opens) [QuasiCompact U.ι]
    (s : S) (hsU : s ∉ (U : Set S)) (hUU' : U ≤ U') (hsU' : s ∈ (U' : Set S))
    (X' : FinitePresentationOver U'.toScheme)
    (G : finitePresentationStalkGluingCategory S U s)
    (hOpenIso : Nonempty (FinitePresentationOver.restrictOverObject hUU' X' ≅ G.fst.obj))
    (hStalkIso : Nonempty
      (FinitePresentationOver.baseChangeOverObject (U'.fromSpecStalkOfMem s hsU') X' ≅
        G.snd.obj))
    (hopen : IsFinite (Comma.hom G.fst.obj))
    (hstalk : IsFinite (Comma.hom G.snd.obj)) :
    ∃ (W : S.Opens) (hUW : U ≤ W) (hWU' : W ≤ U'),
      s ∈ (W : Set S) ∧
        IsFinite (FinitePresentationOver.restrictOverObject hWU' X').hom := sorry

/-- If the open and stalk components of a finite-presentation gluing object are étale, then
the object is étale over some smaller open neighborhood containing the fixed open. -/
theorem existsOpenNeighborhood_etale_of_object_components
    (S : Scheme.{u}) (U U' : S.Opens) [QuasiCompact U.ι]
    (s : S) (hsU : s ∉ (U : Set S)) (hUU' : U ≤ U') (hsU' : s ∈ (U' : Set S))
    (X' : FinitePresentationOver U'.toScheme)
    (G : finitePresentationStalkGluingCategory S U s)
    (hOpenIso : Nonempty (FinitePresentationOver.restrictOverObject hUU' X' ≅ G.fst.obj))
    (hStalkIso : Nonempty
      (FinitePresentationOver.baseChangeOverObject (U'.fromSpecStalkOfMem s hsU') X' ≅
        G.snd.obj))
    (hopen : Etale (Comma.hom G.fst.obj))
    (hstalk : Etale (Comma.hom G.snd.obj)) :
    ∃ (W : S.Opens) (hUW : U ≤ W) (hWU' : W ≤ U'),
      s ∈ (W : Set S) ∧
        Etale (FinitePresentationOver.restrictOverObject hWU' X').hom := sorry

/-- If the open and stalk components of a morphism of finite-presentation gluing objects are
separated, then the morphism is separated over some smaller open neighborhood containing the
fixed open. -/
theorem existsOpenNeighborhood_isSeparated_of_morphism_components
    (S : Scheme.{u}) (U U' : S.Opens) [QuasiCompact U.ι]
    (s : S) (hsU : s ∉ (U : Set S)) (hUU' : U ≤ U') (hsU' : s ∈ (U' : Set S))
    {X₁ X₂ : FinitePresentationOver U'.toScheme} (a : X₁ ⟶ X₂)
    {G₁ G₂ : finitePresentationStalkGluingCategory S U s} (α : G₁ ⟶ G₂)
    (hOpenComm : ∃ (e₁ : FinitePresentationOver.restrictOverObject hUU' X₁ ≅ G₁.fst.obj)
        (e₂ : FinitePresentationOver.restrictOverObject hUU' X₂ ≅ G₂.fst.obj),
      FinitePresentationOver.restrictOverHom hUU' a =
        e₁.hom ≫ (FinitePresentationOver.inclusion U.toScheme).map α.fst ≫ e₂.inv)
    (hStalkComm : ∃
        (e₁ : FinitePresentationOver.baseChangeOverObject
          (U'.fromSpecStalkOfMem s hsU') X₁ ≅ G₁.snd.obj)
        (e₂ : FinitePresentationOver.baseChangeOverObject
          (U'.fromSpecStalkOfMem s hsU') X₂ ≅ G₂.snd.obj),
      FinitePresentationOver.baseChangeOverHom (U'.fromSpecStalkOfMem s hsU') a =
        e₁.hom ≫ (FinitePresentationOver.inclusion (Spec (S.presheaf.stalk s))).map α.snd ≫
          e₂.inv)
    (hopen : IsSeparated (FinitePresentationOver.underlyingHom α.fst))
    (hstalk : IsSeparated (FinitePresentationOver.underlyingHom α.snd)) :
    ∃ (W : S.Opens) (hUW : U ≤ W) (hWU' : W ≤ U'),
      s ∈ (W : Set S) ∧
        IsSeparated (FinitePresentationOver.restrictOverHom hWU' a).left := sorry

/-- If the open and stalk components of a morphism of finite-presentation gluing objects are
proper, then the morphism is proper over some smaller open neighborhood containing the fixed
open. -/
theorem existsOpenNeighborhood_isProper_of_morphism_components
    (S : Scheme.{u}) (U U' : S.Opens) [QuasiCompact U.ι]
    (s : S) (hsU : s ∉ (U : Set S)) (hUU' : U ≤ U') (hsU' : s ∈ (U' : Set S))
    {X₁ X₂ : FinitePresentationOver U'.toScheme} (a : X₁ ⟶ X₂)
    {G₁ G₂ : finitePresentationStalkGluingCategory S U s} (α : G₁ ⟶ G₂)
    (hOpenComm : ∃ (e₁ : FinitePresentationOver.restrictOverObject hUU' X₁ ≅ G₁.fst.obj)
        (e₂ : FinitePresentationOver.restrictOverObject hUU' X₂ ≅ G₂.fst.obj),
      FinitePresentationOver.restrictOverHom hUU' a =
        e₁.hom ≫ (FinitePresentationOver.inclusion U.toScheme).map α.fst ≫ e₂.inv)
    (hStalkComm : ∃
        (e₁ : FinitePresentationOver.baseChangeOverObject
          (U'.fromSpecStalkOfMem s hsU') X₁ ≅ G₁.snd.obj)
        (e₂ : FinitePresentationOver.baseChangeOverObject
          (U'.fromSpecStalkOfMem s hsU') X₂ ≅ G₂.snd.obj),
      FinitePresentationOver.baseChangeOverHom (U'.fromSpecStalkOfMem s hsU') a =
        e₁.hom ≫ (FinitePresentationOver.inclusion (Spec (S.presheaf.stalk s))).map α.snd ≫
          e₂.inv)
    (hopen : IsProper (FinitePresentationOver.underlyingHom α.fst))
    (hstalk : IsProper (FinitePresentationOver.underlyingHom α.snd)) :
    ∃ (W : S.Opens) (hUW : U ≤ W) (hWU' : W ≤ U'),
      s ∈ (W : Set S) ∧
        IsProper (FinitePresentationOver.restrictOverHom hWU' a).left := sorry

/-- If the open and stalk components of a morphism of finite-presentation gluing objects are
finite, then the morphism is finite over some smaller open neighborhood containing the fixed
open. -/
theorem existsOpenNeighborhood_isFinite_of_morphism_components
    (S : Scheme.{u}) (U U' : S.Opens) [QuasiCompact U.ι]
    (s : S) (hsU : s ∉ (U : Set S)) (hUU' : U ≤ U') (hsU' : s ∈ (U' : Set S))
    {X₁ X₂ : FinitePresentationOver U'.toScheme} (a : X₁ ⟶ X₂)
    {G₁ G₂ : finitePresentationStalkGluingCategory S U s} (α : G₁ ⟶ G₂)
    (hOpenComm : ∃ (e₁ : FinitePresentationOver.restrictOverObject hUU' X₁ ≅ G₁.fst.obj)
        (e₂ : FinitePresentationOver.restrictOverObject hUU' X₂ ≅ G₂.fst.obj),
      FinitePresentationOver.restrictOverHom hUU' a =
        e₁.hom ≫ (FinitePresentationOver.inclusion U.toScheme).map α.fst ≫ e₂.inv)
    (hStalkComm : ∃
        (e₁ : FinitePresentationOver.baseChangeOverObject
          (U'.fromSpecStalkOfMem s hsU') X₁ ≅ G₁.snd.obj)
        (e₂ : FinitePresentationOver.baseChangeOverObject
          (U'.fromSpecStalkOfMem s hsU') X₂ ≅ G₂.snd.obj),
      FinitePresentationOver.baseChangeOverHom (U'.fromSpecStalkOfMem s hsU') a =
        e₁.hom ≫ (FinitePresentationOver.inclusion (Spec (S.presheaf.stalk s))).map α.snd ≫
          e₂.inv)
    (hopen : IsFinite (FinitePresentationOver.underlyingHom α.fst))
    (hstalk : IsFinite (FinitePresentationOver.underlyingHom α.snd)) :
    ∃ (W : S.Opens) (hUW : U ≤ W) (hWU' : W ≤ U'),
      s ∈ (W : Set S) ∧
        IsFinite (FinitePresentationOver.restrictOverHom hWU' a).left := sorry

/-- If the open and stalk components of a morphism of finite-presentation gluing objects are
étale, then the morphism is étale over some smaller open neighborhood containing the fixed open.
-/
theorem existsOpenNeighborhood_etale_of_morphism_components
    (S : Scheme.{u}) (U U' : S.Opens) [QuasiCompact U.ι]
    (s : S) (hsU : s ∉ (U : Set S)) (hUU' : U ≤ U') (hsU' : s ∈ (U' : Set S))
    {X₁ X₂ : FinitePresentationOver U'.toScheme} (a : X₁ ⟶ X₂)
    {G₁ G₂ : finitePresentationStalkGluingCategory S U s} (α : G₁ ⟶ G₂)
    (hOpenComm : ∃ (e₁ : FinitePresentationOver.restrictOverObject hUU' X₁ ≅ G₁.fst.obj)
        (e₂ : FinitePresentationOver.restrictOverObject hUU' X₂ ≅ G₂.fst.obj),
      FinitePresentationOver.restrictOverHom hUU' a =
        e₁.hom ≫ (FinitePresentationOver.inclusion U.toScheme).map α.fst ≫ e₂.inv)
    (hStalkComm : ∃
        (e₁ : FinitePresentationOver.baseChangeOverObject
          (U'.fromSpecStalkOfMem s hsU') X₁ ≅ G₁.snd.obj)
        (e₂ : FinitePresentationOver.baseChangeOverObject
          (U'.fromSpecStalkOfMem s hsU') X₂ ≅ G₂.snd.obj),
      FinitePresentationOver.baseChangeOverHom (U'.fromSpecStalkOfMem s hsU') a =
        e₁.hom ≫ (FinitePresentationOver.inclusion (Spec (S.presheaf.stalk s))).map α.snd ≫
          e₂.inv)
    (hopen : Etale (FinitePresentationOver.underlyingHom α.fst))
    (hstalk : Etale (FinitePresentationOver.underlyingHom α.snd)) :
    ∃ (W : S.Opens) (hUW : U ≤ W) (hWU' : W ≤ U'),
      s ∈ (W : Set S) ∧
        Etale (FinitePresentationOver.restrictOverHom hWU' a).left := sorry

end AlgebraicGeometry.FinitePresentationOver.StalkGluing
