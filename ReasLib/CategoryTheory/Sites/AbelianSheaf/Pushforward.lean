/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.RegularEpi
public import ReasLib.CategoryTheory.Adjunction.Abelian
public import ReasLib.CategoryTheory.Sites.LocallySurjective
public import ReasLib.CategoryTheory.Sites.Pullback.SheafCompose
import Mathlib.Tactic.CrossRefAttribute

/-!
# Direct image of sheaves of abelian groups

This file transfers epimorphism preservation from the underlying type-valued direct image to the
direct image of sheaves of abelian groups. Together with the generic exactness criterion for right
adjoints, it gives atomic exactness criteria for continuous direct image.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory.Functor.AbelianPushforward

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D) [u.IsContinuous J K]

/-- Epimorphism preservation by the type-valued direct image transfers to the direct image of
sheaves of abelian groups through the canonical coefficient-forgetful square. -/
theorem preservesEpi_of_underlying
    [J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [K.HasSheafCompose (forget AddCommGrpCat.{w})]
    [(sheafCompose K (forget AddCommGrpCat.{w})).PreservesEpimorphisms]
    (h : (u.sheafPushforwardContinuous (Type w) J K).PreservesEpimorphisms) :
    (u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).PreservesEpimorphisms := sorry

/-- Explicit-evidence bridge for exactness of an additive continuous direct image which
preserves epimorphisms. This form avoids forcing callers with a witness to introduce `letI`. -/
theorem exact_of_preservesEpimorphisms_of
    [Abelian (Sheaf K AddCommGrpCat.{w})] [Abelian (Sheaf J AddCommGrpCat.{w})]
    [(u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]
    (h : (u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).PreservesEpimorphisms) :
    exactFunctor _ _ (u.sheafPushforwardContinuous AddCommGrpCat.{w} J K) := sorry

/-- Lemma 18.15.2 (2): an additive continuous direct image which preserves epimorphisms is
exact. The canonical interface infers the coherent epimorphism-preservation property. -/
@[stacks 04DB "abelian epimorphisms"]
theorem exact_of_preservesEpimorphisms
    [Abelian (Sheaf K AddCommGrpCat.{w})] [Abelian (Sheaf J AddCommGrpCat.{w})]
    [(u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]
    [(u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).PreservesEpimorphisms] :
    exactFunctor _ _ (u.sheafPushforwardContinuous AddCommGrpCat.{w} J K) := sorry

/-- Lemma 18.15.2 (1): preservation of epimorphisms by the underlying type-valued direct image
implies exactness of the additive direct image. -/
@[stacks 04DB "underlying epimorphisms"]
theorem exact_of_underlyingEpi
    [Abelian (Sheaf K AddCommGrpCat.{w})] [Abelian (Sheaf J AddCommGrpCat.{w})]
    [(u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]
    [J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [K.HasSheafCompose (forget AddCommGrpCat.{w})]
    [(sheafCompose K (forget AddCommGrpCat.{w})).PreservesEpimorphisms]
    (h : (u.sheafPushforwardContinuous (Type w) J K).PreservesEpimorphisms) :
    exactFunctor _ _ (u.sheafPushforwardContinuous AddCommGrpCat.{w} J K) := sorry

/-- Lemma 18.15.2 (3): preservation of coequalizers by the underlying type-valued direct image
implies exactness of the additive direct image. -/
@[stacks 04DB "underlying coequalizers"]
theorem exact_of_underlyingCoequalizers
    [Abelian (Sheaf K AddCommGrpCat.{w})] [Abelian (Sheaf J AddCommGrpCat.{w})]
    [(u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]
    [J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [K.HasSheafCompose (forget AddCommGrpCat.{w})]
    [(sheafCompose K (forget AddCommGrpCat.{w})).PreservesEpimorphisms]
    [IsRegularEpiCategory (Sheaf K (Type w))]
    (h : PreservesColimitsOfShape WalkingParallelPair
      (u.sheafPushforwardContinuous (Type w) J K)) :
    exactFunctor _ _ (u.sheafPushforwardContinuous AddCommGrpCat.{w} J K) := sorry

/-- Lemma 18.15.2 (4): preservation of pushouts by the underlying type-valued direct image
implies exactness of the additive direct image. -/
@[stacks 04DB "underlying pushouts"]
theorem exact_of_underlyingPushouts
    [Abelian (Sheaf K AddCommGrpCat.{w})] [Abelian (Sheaf J AddCommGrpCat.{w})]
    [(u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]
    [J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [K.HasSheafCompose (forget AddCommGrpCat.{w})]
    [(sheafCompose K (forget AddCommGrpCat.{w})).PreservesEpimorphisms]
    (h : PreservesColimitsOfShape WalkingSpan
      (u.sheafPushforwardContinuous (Type w) J K)) :
    exactFunctor _ _ (u.sheafPushforwardContinuous AddCommGrpCat.{w} J K) := sorry

namespace Comparison

variable {G : Sheaf K (Type w) ⥤ Sheaf J (Type w)}

/-- Exactness transfers from epimorphism preservation by any functor canonically isomorphic to
the underlying type-valued direct image. -/
theorem exact_of_epi
    [Abelian (Sheaf K AddCommGrpCat.{w})] [Abelian (Sheaf J AddCommGrpCat.{w})]
    [(u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]
    [J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [K.HasSheafCompose (forget AddCommGrpCat.{w})]
    [(sheafCompose K (forget AddCommGrpCat.{w})).PreservesEpimorphisms]
    (e : u.sheafPushforwardContinuous (Type w) J K ≅ G)
    (h : G.PreservesEpimorphisms) :
    exactFunctor _ _ (u.sheafPushforwardContinuous AddCommGrpCat.{w} J K) := sorry

/-- Exactness transfers from coequalizer preservation by any functor canonically isomorphic to
the underlying type-valued direct image. -/
theorem exact_of_coequalizers
    [Abelian (Sheaf K AddCommGrpCat.{w})] [Abelian (Sheaf J AddCommGrpCat.{w})]
    [(u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]
    [J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [K.HasSheafCompose (forget AddCommGrpCat.{w})]
    [(sheafCompose K (forget AddCommGrpCat.{w})).PreservesEpimorphisms]
    [IsRegularEpiCategory (Sheaf K (Type w))]
    (e : u.sheafPushforwardContinuous (Type w) J K ≅ G)
    (h : PreservesColimitsOfShape WalkingParallelPair G) :
    exactFunctor _ _ (u.sheafPushforwardContinuous AddCommGrpCat.{w} J K) := sorry

/-- Exactness transfers from pushout preservation by any functor canonically isomorphic to the
underlying type-valued direct image. -/
theorem exact_of_pushouts
    [Abelian (Sheaf K AddCommGrpCat.{w})] [Abelian (Sheaf J AddCommGrpCat.{w})]
    [(u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]
    [J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [K.HasSheafCompose (forget AddCommGrpCat.{w})]
    [(sheafCompose K (forget AddCommGrpCat.{w})).PreservesEpimorphisms]
    (e : u.sheafPushforwardContinuous (Type w) J K ≅ G)
    (h : PreservesColimitsOfShape WalkingSpan G) :
    exactFunctor _ _ (u.sheafPushforwardContinuous AddCommGrpCat.{w} J K) := sorry

end Comparison

end CategoryTheory.Functor.AbelianPushforward
