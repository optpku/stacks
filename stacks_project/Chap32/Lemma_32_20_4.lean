/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Over.StalkGluing.Neighborhood
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 32.20.4 (1): if the open and stalk components corresponding to a finitely presented
object over `U'` are separated, then after shrinking `U'` around `s` while retaining `U`, its
restriction is separated. -/
@[stacks 0EY3]
#check
  (AlgebraicGeometry.FinitePresentationOver.StalkGluing.existsOpenNeighborhood_isSeparated_of_object_components :
    ∀ (S : Scheme.{u}) (U U' : S.Opens) [QuasiCompact U.ι]
      (s : S) (hsU : s ∉ (U : Set S)) (hUU' : U ≤ U') (hsU' : s ∈ (U' : Set S))
      (X' : FinitePresentationOver U'.toScheme)
      (G : finitePresentationStalkGluingCategory S U s)
      (hOpenIso : Nonempty (FinitePresentationOver.restrictOverObject hUU' X' ≅ G.fst.obj))
      (hStalkIso : Nonempty
        (FinitePresentationOver.baseChangeOverObject (U'.fromSpecStalkOfMem s hsU') X' ≅
          G.snd.obj))
      (hopen : IsSeparated (Comma.hom G.fst.obj))
      (hstalk : IsSeparated (Comma.hom G.snd.obj)),
      ∃ (W : S.Opens) (hUW : U ≤ W) (hWU' : W ≤ U'),
        s ∈ (W : Set S) ∧
          IsSeparated (FinitePresentationOver.restrictOverObject hWU' X').hom)

/- Lemma 32.20.4 (2): if the open and stalk components corresponding to a finitely presented
object over `U'` are proper, then after shrinking `U'` around `s` while retaining `U`, its
restriction is proper. -/
@[stacks 0EY3]
#check
  (AlgebraicGeometry.FinitePresentationOver.StalkGluing.existsOpenNeighborhood_isProper_of_object_components :
    ∀ (S : Scheme.{u}) (U U' : S.Opens) [QuasiCompact U.ι]
      (s : S) (hsU : s ∉ (U : Set S)) (hUU' : U ≤ U') (hsU' : s ∈ (U' : Set S))
      (X' : FinitePresentationOver U'.toScheme)
      (G : finitePresentationStalkGluingCategory S U s)
      (hOpenIso : Nonempty (FinitePresentationOver.restrictOverObject hUU' X' ≅ G.fst.obj))
      (hStalkIso : Nonempty
        (FinitePresentationOver.baseChangeOverObject (U'.fromSpecStalkOfMem s hsU') X' ≅
          G.snd.obj))
      (hopen : IsProper (Comma.hom G.fst.obj))
      (hstalk : IsProper (Comma.hom G.snd.obj)),
      ∃ (W : S.Opens) (hUW : U ≤ W) (hWU' : W ≤ U'),
        s ∈ (W : Set S) ∧
          IsProper (FinitePresentationOver.restrictOverObject hWU' X').hom)

/- Lemma 32.20.4 (3): if the open and stalk components corresponding to a finitely presented
object over `U'` are finite, then after shrinking `U'` around `s` while retaining `U`, its
restriction is finite. -/
@[stacks 0EY3]
#check
  (AlgebraicGeometry.FinitePresentationOver.StalkGluing.existsOpenNeighborhood_isFinite_of_object_components :
    ∀ (S : Scheme.{u}) (U U' : S.Opens) [QuasiCompact U.ι]
      (s : S) (hsU : s ∉ (U : Set S)) (hUU' : U ≤ U') (hsU' : s ∈ (U' : Set S))
      (X' : FinitePresentationOver U'.toScheme)
      (G : finitePresentationStalkGluingCategory S U s)
      (hOpenIso : Nonempty (FinitePresentationOver.restrictOverObject hUU' X' ≅ G.fst.obj))
      (hStalkIso : Nonempty
        (FinitePresentationOver.baseChangeOverObject (U'.fromSpecStalkOfMem s hsU') X' ≅
          G.snd.obj))
      (hopen : IsFinite (Comma.hom G.fst.obj))
      (hstalk : IsFinite (Comma.hom G.snd.obj)),
      ∃ (W : S.Opens) (hUW : U ≤ W) (hWU' : W ≤ U'),
        s ∈ (W : Set S) ∧
          IsFinite (FinitePresentationOver.restrictOverObject hWU' X').hom)

/- Lemma 32.20.4 (4): if the open and stalk components corresponding to a finitely presented
object over `U'` are étale, then after shrinking `U'` around `s` while retaining `U`, its
restriction is étale. -/
@[stacks 0EY3]
#check
  (AlgebraicGeometry.FinitePresentationOver.StalkGluing.existsOpenNeighborhood_etale_of_object_components :
    ∀ (S : Scheme.{u}) (U U' : S.Opens) [QuasiCompact U.ι]
      (s : S) (hsU : s ∉ (U : Set S)) (hUU' : U ≤ U') (hsU' : s ∈ (U' : Set S))
      (X' : FinitePresentationOver U'.toScheme)
      (G : finitePresentationStalkGluingCategory S U s)
      (hOpenIso : Nonempty (FinitePresentationOver.restrictOverObject hUU' X' ≅ G.fst.obj))
      (hStalkIso : Nonempty
        (FinitePresentationOver.baseChangeOverObject (U'.fromSpecStalkOfMem s hsU') X' ≅
          G.snd.obj))
      (hopen : Etale (Comma.hom G.fst.obj))
      (hstalk : Etale (Comma.hom G.snd.obj)),
      ∃ (W : S.Opens) (hUW : U ≤ W) (hWU' : W ≤ U'),
        s ∈ (W : Set S) ∧
          Etale (FinitePresentationOver.restrictOverObject hWU' X').hom)

/- Lemma 32.20.4 (5): if the open and stalk components corresponding to a morphism of
finite-presentation objects over `U'` are separated, then after shrinking `U'` around `s` while
retaining `U`, its restriction is separated. -/
@[stacks 0EY3]
#check
  (AlgebraicGeometry.FinitePresentationOver.StalkGluing.existsOpenNeighborhood_isSeparated_of_morphism_components :
    ∀ (S : Scheme.{u}) (U U' : S.Opens) [QuasiCompact U.ι]
      (s : S) (hsU : s ∉ (U : Set S)) (hUU' : U ≤ U') (hsU' : s ∈ (U' : Set S))
      {X₁ X₂ : FinitePresentationOver U'.toScheme} (a : X₁ ⟶ X₂)
      {G₁ G₂ : finitePresentationStalkGluingCategory S U s} (α : G₁ ⟶ G₂)
      (hOpenComm : ∃
        (e₁ : FinitePresentationOver.restrictOverObject hUU' X₁ ≅ G₁.fst.obj)
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
      (hstalk : IsSeparated (FinitePresentationOver.underlyingHom α.snd)),
      ∃ (W : S.Opens) (hUW : U ≤ W) (hWU' : W ≤ U'),
        s ∈ (W : Set S) ∧
          IsSeparated (FinitePresentationOver.restrictOverHom hWU' a).left)

/- Lemma 32.20.4 (6): if the open and stalk components corresponding to a morphism of
finite-presentation objects over `U'` are proper, then after shrinking `U'` around `s` while
retaining `U`, its restriction is proper. -/
@[stacks 0EY3]
#check
  (AlgebraicGeometry.FinitePresentationOver.StalkGluing.existsOpenNeighborhood_isProper_of_morphism_components :
    ∀ (S : Scheme.{u}) (U U' : S.Opens) [QuasiCompact U.ι]
      (s : S) (hsU : s ∉ (U : Set S)) (hUU' : U ≤ U') (hsU' : s ∈ (U' : Set S))
      {X₁ X₂ : FinitePresentationOver U'.toScheme} (a : X₁ ⟶ X₂)
      {G₁ G₂ : finitePresentationStalkGluingCategory S U s} (α : G₁ ⟶ G₂)
      (hOpenComm : ∃
        (e₁ : FinitePresentationOver.restrictOverObject hUU' X₁ ≅ G₁.fst.obj)
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
      (hstalk : IsProper (FinitePresentationOver.underlyingHom α.snd)),
      ∃ (W : S.Opens) (hUW : U ≤ W) (hWU' : W ≤ U'),
        s ∈ (W : Set S) ∧
          IsProper (FinitePresentationOver.restrictOverHom hWU' a).left)

/- Lemma 32.20.4 (7): if the open and stalk components corresponding to a morphism of
finite-presentation objects over `U'` are finite, then after shrinking `U'` around `s` while
retaining `U`, its restriction is finite. -/
@[stacks 0EY3]
#check
  (AlgebraicGeometry.FinitePresentationOver.StalkGluing.existsOpenNeighborhood_isFinite_of_morphism_components :
    ∀ (S : Scheme.{u}) (U U' : S.Opens) [QuasiCompact U.ι]
      (s : S) (hsU : s ∉ (U : Set S)) (hUU' : U ≤ U') (hsU' : s ∈ (U' : Set S))
      {X₁ X₂ : FinitePresentationOver U'.toScheme} (a : X₁ ⟶ X₂)
      {G₁ G₂ : finitePresentationStalkGluingCategory S U s} (α : G₁ ⟶ G₂)
      (hOpenComm : ∃
        (e₁ : FinitePresentationOver.restrictOverObject hUU' X₁ ≅ G₁.fst.obj)
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
      (hstalk : IsFinite (FinitePresentationOver.underlyingHom α.snd)),
      ∃ (W : S.Opens) (hUW : U ≤ W) (hWU' : W ≤ U'),
        s ∈ (W : Set S) ∧
          IsFinite (FinitePresentationOver.restrictOverHom hWU' a).left)

/- Lemma 32.20.4 (8): if the open and stalk components corresponding to a morphism of
finite-presentation objects over `U'` are étale, then after shrinking `U'` around `s` while
retaining `U`, its restriction is étale. -/
@[stacks 0EY3]
#check
  (AlgebraicGeometry.FinitePresentationOver.StalkGluing.existsOpenNeighborhood_etale_of_morphism_components :
    ∀ (S : Scheme.{u}) (U U' : S.Opens) [QuasiCompact U.ι]
      (s : S) (hsU : s ∉ (U : Set S)) (hUU' : U ≤ U') (hsU' : s ∈ (U' : Set S))
      {X₁ X₂ : FinitePresentationOver U'.toScheme} (a : X₁ ⟶ X₂)
      {G₁ G₂ : finitePresentationStalkGluingCategory S U s} (α : G₁ ⟶ G₂)
      (hOpenComm : ∃
        (e₁ : FinitePresentationOver.restrictOverObject hUU' X₁ ≅ G₁.fst.obj)
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
      (hstalk : Etale (FinitePresentationOver.underlyingHom α.snd)),
      ∃ (W : S.Opens) (hUW : U ≤ W) (hWU' : W ≤ U'),
        s ∈ (W : Set S) ∧
          Etale (FinitePresentationOver.restrictOverHom hWU' a).left)
