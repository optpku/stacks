/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tensor.Bifunctor
public import ReasLib.CategoryTheory.Adjunction.RelativeCupProduct
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Kunneth

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.Kunneth

/-- Derived global sections of a scheme over a base, with scalars restricted to the base's
global section ring. -/
abbrev globalSectionsOver {X S : Scheme.{u}} (a : X ⟶ S) :
    DerivedCategory X.Modules ⥤
      DerivedCategory (ModuleCat (Scheme.globalSectionsRing S)) :=
  RingedSpace.Module.Derived.GlobalSections.functor X.toRingedSpace ⋙
    ModuleCat.derivedRestrictionOfScalars a.appTop.hom

/-- `globalSectionsOver` is derived global sections followed by restriction of scalars to the
base's global section ring. -/
theorem globalSectionsOver_def {X S : Scheme.{u}} (a : X ⟶ S) :
    globalSectionsOver a =
      RingedSpace.Module.Derived.GlobalSections.functor X.toRingedSpace ⋙
        ModuleCat.derivedRestrictionOfScalars a.appTop.hom := sorry

/-- The canonical derived pullback on module sheaves along a morphism of schemes. -/
abbrev pullbackDerived {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory Y.Modules ⥤ DerivedCategory X.Modules :=
  RingedSpace.modulePullbackDerived f.toLRSHom.toShHom

/-- `pullbackDerived` is the ringed-space derived pullback associated to a scheme morphism. -/
theorem pullbackDerived_def {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullbackDerived f = RingedSpace.modulePullbackDerived f.toLRSHom.toShHom := sorry

/-- A tensor-compatible adjunction model for derived global sections of `P` over the global
section ring of `S`. -/
abbrev BaseTensorModel {P S : Scheme.{u}} (c : P ⟶ S)
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends P.toRingedSpace]
    [RingedSpace.ModuleDerived.Tensor.Has P.toRingedSpace] :=
  CategoryTheory.Adjunction.TensorModel
    (globalSectionsOver c)
    (RingedSpace.ModuleDerived.Tensor.globalSectionsCurried S.toRingedSpace)
    (RingedSpace.ModuleDerived.Tensor.curried P.toRingedSpace)

/-- `BaseTensorModel` is the relative tensor model attached to derived global sections. -/
theorem BaseTensorModel_def {P S : Scheme.{u}} (c : P ⟶ S)
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends P.toRingedSpace]
    [RingedSpace.ModuleDerived.Tensor.Has P.toRingedSpace] :
    BaseTensorModel c =
      CategoryTheory.Adjunction.TensorModel
        (globalSectionsOver c)
        (RingedSpace.ModuleDerived.Tensor.globalSectionsCurried S.toRingedSpace)
        (RingedSpace.ModuleDerived.Tensor.curried P.toRingedSpace) := sorry

/-- The global Künneth composite associated to specified pullback maps and an
`A`-linear tensor-compatible derived-global-sections model, where `A = Γ(S, ⊤)`. -/
noncomputable def globalMapOf {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends
      (Limits.pullback a b).toRingedSpace]
    [RingedSpace.ModuleDerived.Tensor.Has (Limits.pullback a b).toRingedSpace]
    (K : DerivedCategory X.Modules) (M : DerivedCategory Y.Modules)
    (model : BaseTensorModel (Limits.pullback.fst a b ≫ a))
    (pullK : (globalSectionsOver a).obj K ⟶
      (globalSectionsOver (Limits.pullback.fst a b ≫ a)).obj
        ((pullbackDerived (Limits.pullback.fst a b)).obj K))
    (pullM : (globalSectionsOver b).obj M ⟶
      (globalSectionsOver (Limits.pullback.fst a b ≫ a)).obj
        ((pullbackDerived (Limits.pullback.snd a b)).obj M)) :
    RingedSpace.ModuleDerived.Tensor.globalSectionsObj S.toRingedSpace
        ((globalSectionsOver a).obj K) ((globalSectionsOver b).obj M) ⟶
      (globalSectionsOver (Limits.pullback.fst a b ≫ a)).obj
        (RingedSpace.ModuleDerived.Tensor.obj
          ((pullbackDerived (Limits.pullback.fst a b)).obj K)
          ((pullbackDerived (Limits.pullback.snd a b)).obj M)) :=
  RingedSpace.ModuleDerived.Tensor.globalSectionsMap S.toRingedSpace pullK pullM ≫
    model.cupProduct
      ((pullbackDerived (Limits.pullback.fst a b)).obj K)
      ((pullbackDerived (Limits.pullback.snd a b)).obj M)

/-- The modeled global Künneth composite is the tensor of its specified pullback components
followed by the relative derived cup product. -/
theorem globalMapOf_spec {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends
      (Limits.pullback a b).toRingedSpace]
    [RingedSpace.ModuleDerived.Tensor.Has (Limits.pullback a b).toRingedSpace]
    (K : DerivedCategory X.Modules) (M : DerivedCategory Y.Modules)
    (model : BaseTensorModel (Limits.pullback.fst a b ≫ a))
    (pullK : (globalSectionsOver a).obj K ⟶
      (globalSectionsOver (Limits.pullback.fst a b ≫ a)).obj
        ((pullbackDerived (Limits.pullback.fst a b)).obj K))
    (pullM : (globalSectionsOver b).obj M ⟶
      (globalSectionsOver (Limits.pullback.fst a b ≫ a)).obj
        ((pullbackDerived (Limits.pullback.snd a b)).obj M)) :
    globalMapOf a b K M model pullK pullM =
      RingedSpace.ModuleDerived.Tensor.globalSectionsMap S.toRingedSpace pullK pullM ≫
        model.cupProduct
          ((pullbackDerived (Limits.pullback.fst a b)).obj K)
          ((pullbackDerived (Limits.pullback.snd a b)).obj M) := sorry

/-- The canonical global Künneth morphism, obtained from the lax-monoidal comparison for
derived global sections and the scheme-level derived Künneth morphism. -/
noncomputable def globalMap {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends S.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends S.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization S.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends
      (Limits.pullback a b).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends (Limits.pullback a b).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization (Limits.pullback a b).toRingedSpace]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom a.toShHom)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom b.toShHom)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom (Limits.pullback.fst a b).toShHom)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom (Limits.pullback.snd a b).toShHom)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom (Limits.pullback.fst a b ≫ a).toShHom)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom (Limits.pullback.snd a b ≫ b).toShHom)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom
        ((Limits.pullback.fst a b).toShHom ≫ a.toShHom))]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom
        ((Limits.pullback.snd a b).toShHom ≫ b.toShHom))]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison
      (Limits.pullback.fst a b).toShHom a.toShHom)]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison
      (Limits.pullback.snd a b).toShHom b.toShHom)]
    [(RingedSpace.modulePullbackDerived
      (Limits.pullback.fst a b ≫ a).toShHom).OplaxMonoidal]
    [MonoidalCategory
      (RingedSpace.ModuleDerived.Tensor.globalSectionsDerived S.toRingedSpace)]
    [(RingedSpace.Module.Derived.GlobalSections.functor S.toRingedSpace).LaxMonoidal]
    (K : DerivedCategory X.Modules) (M : DerivedCategory Y.Modules) :
    (RingedSpace.Module.Derived.GlobalSections.functor S.toRingedSpace).obj
          ((RingedSpace.moduleDerivedPushforward a.toShHom).obj K) ⊗
        (RingedSpace.Module.Derived.GlobalSections.functor S.toRingedSpace).obj
          ((RingedSpace.moduleDerivedPushforward b.toShHom).obj M) ⟶
      (RingedSpace.Module.Derived.GlobalSections.functor S.toRingedSpace).obj
        ((RingedSpace.moduleDerivedPushforward
          (Limits.pullback.fst a b ≫ a).toShHom).obj
            (Scheme.ModuleDerived.Kunneth.externalTensorProduct a b K M)) :=
  Functor.LaxMonoidal.μ (RingedSpace.Module.Derived.GlobalSections.functor S.toRingedSpace)
      ((RingedSpace.moduleDerivedPushforward a.toShHom).obj K)
      ((RingedSpace.moduleDerivedPushforward b.toShHom).obj M) ≫
    (RingedSpace.Module.Derived.GlobalSections.functor S.toRingedSpace).map
      (Scheme.ModuleDerived.Kunneth.map a b K M)

/-- The global Künneth morphism is the global-sections tensor comparison followed by derived
global sections of the canonical scheme-level Künneth morphism. -/
theorem globalMap_spec {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends S.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends S.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization S.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends
      (Limits.pullback a b).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends (Limits.pullback a b).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization (Limits.pullback a b).toRingedSpace]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom a.toShHom)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom b.toShHom)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom (Limits.pullback.fst a b).toShHom)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom (Limits.pullback.snd a b).toShHom)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom (Limits.pullback.fst a b ≫ a).toShHom)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom (Limits.pullback.snd a b ≫ b).toShHom)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom
        ((Limits.pullback.fst a b).toShHom ≫ a.toShHom))]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom
        ((Limits.pullback.snd a b).toShHom ≫ b.toShHom))]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison
      (Limits.pullback.fst a b).toShHom a.toShHom)]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison
      (Limits.pullback.snd a b).toShHom b.toShHom)]
    [(RingedSpace.modulePullbackDerived
      (Limits.pullback.fst a b ≫ a).toShHom).OplaxMonoidal]
    [MonoidalCategory
      (RingedSpace.ModuleDerived.Tensor.globalSectionsDerived S.toRingedSpace)]
    [(RingedSpace.Module.Derived.GlobalSections.functor S.toRingedSpace).LaxMonoidal]
    (K : DerivedCategory X.Modules) (M : DerivedCategory Y.Modules) :
    globalMap a b K M =
      Functor.LaxMonoidal.μ (RingedSpace.Module.Derived.GlobalSections.functor S.toRingedSpace)
          ((RingedSpace.moduleDerivedPushforward a.toShHom).obj K)
          ((RingedSpace.moduleDerivedPushforward b.toShHom).obj M) ≫
        (RingedSpace.Module.Derived.GlobalSections.functor S.toRingedSpace).map
          (Scheme.ModuleDerived.Kunneth.map a b K M) := sorry

end AlgebraicGeometry.Scheme.Modules.Kunneth

end
