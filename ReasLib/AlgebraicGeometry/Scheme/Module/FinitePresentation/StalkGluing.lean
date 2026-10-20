module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation.Gluing
public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Over.StalkGluing
import Mathlib.Tactic.CrossRefAttribute

/-!
# Gluing finitely presented modules over a stalk

This leaf records the categorical gluing equivalence for finitely presented modules over the
complement of a closed point and the local scheme at that point.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- The canonical comparison between the two pullbacks of a finitely presented module to the
intersection of an open subscheme with a stalk scheme. -/
noncomputable def finitePresentationModuleStalkGluingIso
    (S : Scheme.{u}) (U : S.Opens) (s : S) :
    FinitePresentationModules.pullback U.ι ⋙
        (FinitePresentationModules.inclusion U.toScheme ⋙
          Scheme.Modules.pullback ((S.fromSpecStalk s) ∣_ U)) ≅
      FinitePresentationModules.pullback (S.fromSpecStalk s) ⋙
        (FinitePresentationModules.inclusion _ ⋙
          Scheme.Modules.pullback (stalkOpenIntersection S U s).ι) :=
  Functor.isoWhiskerLeft (FinitePresentationModules.inclusion S)
    (Scheme.Modules.pullbackComp _ _ ≪≫
      Scheme.Modules.pullbackCongr (morphismRestrict_ι _ _) ≪≫
      (Scheme.Modules.pullbackComp _ _).symm)

/-- Restrict a finitely presented module to an open subscheme and to a stalk scheme, with the
canonical identification of the two pullbacks to their intersection. -/
noncomputable def finitePresentationModuleStalkGluingFunctor
    (S : Scheme.{u}) (U : S.Opens) (s : S) :
    FinitePresentationModules S ⥤
      finitePresentationModuleGluingCategory U (stalkOpenIntersection S U s)
        ((S.fromSpecStalk s) ∣_ U) :=
  (CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback _ _ _).obj
    { fst := FinitePresentationModules.pullback U.ι
      snd := FinitePresentationModules.pullback (S.fromSpecStalk s)
      iso := finitePresentationModuleStalkGluingIso S U s }

/-- The open component of module stalk-gluing is pullback to the open subscheme. -/
@[simp]
theorem finitePresentationModuleStalkGluingFunctor_obj_fst
    (S : Scheme.{u}) (U : S.Opens) (s : S) (ℱ : FinitePresentationModules S) :
    ((finitePresentationModuleStalkGluingFunctor S U s).obj ℱ).fst =
      (FinitePresentationModules.pullback U.ι).obj ℱ := rfl

/-- The stalk component of module stalk-gluing is pullback to the local scheme. -/
@[simp]
theorem finitePresentationModuleStalkGluingFunctor_obj_snd
    (S : Scheme.{u}) (U : S.Opens) (s : S) (ℱ : FinitePresentationModules S) :
    ((finitePresentationModuleStalkGluingFunctor S U s).obj ℱ).snd =
      (FinitePresentationModules.pullback (S.fromSpecStalk s)).obj ℱ := rfl

/-- The gluing isomorphism is the canonical pullback comparison. -/
@[simp]
theorem finitePresentationModuleStalkGluingFunctor_obj_iso
    (S : Scheme.{u}) (U : S.Opens) (s : S) (ℱ : FinitePresentationModules S) :
    ((finitePresentationModuleStalkGluingFunctor S U s).obj ℱ).iso =
      (finitePresentationModuleStalkGluingIso S U s).app ℱ := rfl

/-- For a closed point with quasi-compact complement, the module restriction functor is an
equivalence. -/
@[stacks 0F21]
theorem finitePresentationModuleStalkGluingFunctor_isEquivalence
    (S : Scheme.{u}) (U : S.Opens) [QuasiCompact U.ι]
    (s : S) (hs : s ∈ closedPoints S)
    (hU : (U : Set S) = ({s} : Set S)ᶜ) :
    (finitePresentationModuleStalkGluingFunctor S U s).IsEquivalence := sorry

end AlgebraicGeometry
