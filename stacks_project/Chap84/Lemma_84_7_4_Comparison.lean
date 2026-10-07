module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pullback.Composition
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap84.Lemma_84_7_1_Carrier
public import stacks_project.Chap84.Lemma_84_7_2_Comparison

/-!
# Canonical unbounded derived units along `ε_X` and `a_X`

An object `K` of `D_QCoh(𝒪_X)`, after the objectwise carrier lift to
`ModuleCat.{u + 1}`, has canonical maps
`Lπ_X^* K ⟶ Rε_{X,*}(La_X^* K)` and `K ⟶ Ra_{X,*}(La_X^* K)` in the
unbounded derived category of modules. The first is the derived `ε_X`-unit
at `Lπ_X^* K`, composed with `Rε_{X,*}` of the derived-pullback comparison
for `a_X = π_X ∘ ε_X`; the second is the derived `a_X`-unit.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale
open AlgebraicGeometry.AlgebraicSpace.Fppf
open RingedSite
open RingedSite.Hom
open scoped RingedSiteDerived

noncomputable section

universe u v w

namespace AlgebraicGeometry.AlgebraicSpace.AssociatedModule

/-- A morphism of module sheaves, lifted objectwise by `ModuleCat.uliftFunctor`. -/
def moduleCarrierLiftMap (site : RingedSite.{v, w, u})
    {F G : ModuleCat.{u} site} (f : F ⟶ G) :
    moduleCarrierLift site F ⟶ moduleCarrierLift site G :=
  ⟨{ app := fun U ↦ (ModuleCat.uliftFunctor.{u + 1} _).map (f.val.app U)
     naturality := fun {U V} i ↦ sorry }⟩

/-- The objectwise carrier-universe lift as a functor on module sheaves. -/
def moduleCarrierLiftFunctor (site : RingedSite.{v, w, u}) :
    ModuleCat.{u} site ⥤ ModuleCat.{u + 1} site where
  obj := moduleCarrierLift site
  map := moduleCarrierLiftMap site
  map_id := sorry
  map_comp := sorry

/-- The object map of `moduleCarrierLiftFunctor` is `moduleCarrierLift`. -/
theorem moduleCarrierLiftFunctor_obj (site : RingedSite.{v, w, u})
    (F : ModuleCat.{u} site) :
    (moduleCarrierLiftFunctor site).obj F = moduleCarrierLift site F :=
  rfl

/-- The morphism map of `moduleCarrierLiftFunctor` is `moduleCarrierLiftMap`. -/
theorem moduleCarrierLiftFunctor_map (site : RingedSite.{v, w, u})
    {F G : ModuleCat.{u} site} (f : F ⟶ G) :
    (moduleCarrierLiftFunctor site).map f = moduleCarrierLiftMap site f :=
  rfl

/-- Objectwise carrier lift is additive. -/
instance moduleCarrierLiftFunctor_additive
    (site : RingedSite.{v, w, u}) :
    (moduleCarrierLiftFunctor site).Additive :=
  sorry

/-- Objectwise carrier lift preserves finite limits. -/
instance moduleCarrierLiftFunctor_preservesFiniteLimits
    (site : RingedSite.{v, w, u}) :
    PreservesFiniteLimits (moduleCarrierLiftFunctor site) :=
  sorry

/-- Objectwise carrier lift preserves finite colimits. -/
instance moduleCarrierLiftFunctor_preservesFiniteColimits
    (site : RingedSite.{v, w, u}) :
    PreservesFiniteColimits (moduleCarrierLiftFunctor site) :=
  sorry

variable {S : Scheme.{u}}

/-- Objectwise carrier lift on `(X_étale, 𝒪_X)` is additive. -/
instance moduleCarrierLiftFunctor_ringedSite_additive (X : AlgebraicSpace S) :
    (moduleCarrierLiftFunctor (ringedSite X)).Additive :=
  sorry

/-- Objectwise carrier lift on `(X_étale, 𝒪_X)` preserves finite limits. -/
instance moduleCarrierLiftFunctor_ringedSite_preservesFiniteLimits
    (X : AlgebraicSpace S) :
    PreservesFiniteLimits (moduleCarrierLiftFunctor (ringedSite X)) :=
  sorry

/-- Objectwise carrier lift on `(X_étale, 𝒪_X)` preserves finite colimits. -/
instance moduleCarrierLiftFunctor_ringedSite_preservesFiniteColimits
    (X : AlgebraicSpace S) :
    PreservesFiniteColimits (moduleCarrierLiftFunctor (ringedSite X)) :=
  sorry

/-- Derived objectwise carrier lift from `D(𝒪_X)` to modules of universe `u + 1`
on the small étale ringed site. -/
abbrev moduleCarrierLiftDerived (X : AlgebraicSpace S) :
    AlgebraicGeometry.AlgebraicSpace.ModuleDerived X ⥤
      RingedSite.Hom.ModuleDerived.{u + 1} (ringedSite X) :=
  @Functor.mapDerivedCategory
    (Modules X) inferInstance inferInstance (modulesHasDerivedCategory X)
    (ModuleCat.{u + 1} (ringedSite X)) inferInstance inferInstance
    (moduleCat_hasDerivedCategory.{u + 1} (ringedSite X))
    (moduleCarrierLiftFunctor (ringedSite X))
    inferInstance inferInstance inferInstance

/-- `moduleCarrierLiftDerived` is `mapDerivedCategory` of the objectwise carrier
lift. -/
theorem moduleCarrierLiftDerived_eq (X : AlgebraicSpace S) :
    moduleCarrierLiftDerived X =
      @Functor.mapDerivedCategory
        (Modules X) inferInstance inferInstance (modulesHasDerivedCategory X)
        (ModuleCat.{u + 1} (ringedSite X)) inferInstance inferInstance
        (moduleCat_hasDerivedCategory.{u + 1} (ringedSite X))
        (moduleCarrierLiftFunctor (ringedSite X))
        inferInstance inferInstance inferInstance :=
  rfl

/-- Total left-derived pullback along `π_X` exists at universe `u + 1`. -/
instance etalePi_modulePullbackDerived_hasLeftDerived (X : AlgebraicSpace S)
    [(etalePiRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint] :
    Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{u + 1} (etalePiRingedHom X))
      (ModuleQis.{u + 1} (ringedSite X)) :=
  sorry

/-- Total left-derived pullback along `ε_X` exists at universe `u + 1`. -/
instance epsilon_modulePullbackDerived_hasLeftDerived (X : AlgebraicSpace S)
    [(epsilonRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint] :
    Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{u + 1} (epsilonRingedHom X))
      (ModuleQis.{u + 1} (overEtaleRingedSite X)) :=
  sorry

/-- Total left-derived pullback along `a_X` exists at universe `u + 1`. -/
instance a_modulePullbackDerived_hasLeftDerived (X : AlgebraicSpace S)
    [(aRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint] :
    Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{u + 1} (aRingedHom X))
      (ModuleQis.{u + 1} (ringedSite X)) :=
  sorry

/-- Total left-derived pullback along `π_X ∘ ε_X` exists at universe `u + 1`. -/
instance epsilon_comp_etalePi_modulePullbackDerived_hasLeftDerived
    (X : AlgebraicSpace S)
    [((epsilonRingedHom X).comp (etalePiRingedHom X)).modulePushforward.{u + 1}.IsRightAdjoint] :
    Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{u + 1}
        ((epsilonRingedHom X).comp (etalePiRingedHom X)))
      (ModuleQis.{u + 1} (ringedSite X)) :=
  sorry

/-- The derived pullback-pushforward pair condition for `ε_X`. -/
instance epsilon_moduleDerivedAdjunction_hasPair (X : AlgebraicSpace S)
    [(epsilonRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u + 1} (epsilonRingedHom X))
      (ModuleQis.{u + 1} (overFppfRingedSite X))] :
    DerivedAdjunction.HasPair.{u + 1} (epsilonRingedHom X) :=
  sorry

/-- The derived pullback-pushforward pair condition for `a_X`. -/
instance a_moduleDerivedAdjunction_hasPair (X : AlgebraicSpace S)
    [(aRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u + 1} (aRingedHom X))
      (ModuleQis.{u + 1} (overFppfRingedSite X))] :
    DerivedAdjunction.HasPair.{u + 1} (aRingedHom X) :=
  sorry

/-- The canonical map `Lπ_X^* K ⟶ Rε_{X,*}(La_X^* K)` after the carrier lift. -/
def piPullbackDerivedUnit {X : AlgebraicSpace S}
    (K : RingedSite.Hom.ModuleDerived.{u + 1} (ringedSite X))
    [(etalePiRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint]
    [(epsilonRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint]
    [(aRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u + 1} (epsilonRingedHom X))
      (ModuleQis.{u + 1} (overFppfRingedSite X))] :
    (modulePullbackDerived.{u + 1} (etalePiRingedHom X)).obj K ⟶
      (modulePushforwardDerived.{u + 1} (epsilonRingedHom X)).obj
        ((modulePullbackDerived.{u + 1} (aRingedHom X)).obj K) :=
  (moduleDerivedAdjunction.{u + 1} (epsilonRingedHom X)).unit.app
      ((modulePullbackDerived.{u + 1} (etalePiRingedHom X)).obj K) ≫
    (modulePushforwardDerived.{u + 1} (epsilonRingedHom X)).map
      ((modulePullbackDerived.compComparison.{u + 1}
          (epsilonRingedHom X) (etalePiRingedHom X)).app K)

/-- `piPullbackDerivedUnit` is the derived `ε_X`-unit at `Lπ_X^* K`, followed by
`Rε_{X,*}` of the derived-pullback comparison for `a_X = π_X ∘ ε_X`. -/
theorem piPullbackDerivedUnit_eq {X : AlgebraicSpace S}
    (K : RingedSite.Hom.ModuleDerived.{u + 1} (ringedSite X))
    [(etalePiRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint]
    [(epsilonRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint]
    [(aRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u + 1} (epsilonRingedHom X))
      (ModuleQis.{u + 1} (overFppfRingedSite X))] :
    piPullbackDerivedUnit K =
      (moduleDerivedAdjunction.{u + 1} (epsilonRingedHom X)).unit.app
          ((modulePullbackDerived.{u + 1} (etalePiRingedHom X)).obj K) ≫
        (modulePushforwardDerived.{u + 1} (epsilonRingedHom X)).map
          ((modulePullbackDerived.compComparison.{u + 1}
              (epsilonRingedHom X) (etalePiRingedHom X)).app K) :=
  sorry

/-- The canonical map `K ⟶ Ra_{X,*}(La_X^* K)` after the carrier lift. -/
def aDerivedUnit {X : AlgebraicSpace S}
    (K : RingedSite.Hom.ModuleDerived.{u + 1} (ringedSite X))
    [(aRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u + 1} (aRingedHom X))
      (ModuleQis.{u + 1} (overFppfRingedSite X))] :
    K ⟶
      (modulePushforwardDerived.{u + 1} (aRingedHom X)).obj
        ((modulePullbackDerived.{u + 1} (aRingedHom X)).obj K) :=
  (moduleDerivedAdjunction.{u + 1} (aRingedHom X)).unit.app K

/-- `aDerivedUnit` is the derived `a_X`-adjunction unit. -/
theorem aDerivedUnit_eq {X : AlgebraicSpace S}
    (K : RingedSite.Hom.ModuleDerived.{u + 1} (ringedSite X))
    [(aRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u + 1} (aRingedHom X))
      (ModuleQis.{u + 1} (overFppfRingedSite X))] :
    aDerivedUnit K =
      (moduleDerivedAdjunction.{u + 1} (aRingedHom X)).unit.app K :=
  sorry

/-- For `K` in `D_QCoh(𝒪_X)`, the map `Lπ_X^* K ⟶ Rε_{X,*}(La_X^* K)` is an
isomorphism. -/
theorem piPullbackDerivedUnit_isIso {X : AlgebraicSpace S} (K : DerivedQCoh X)
    [(etalePiRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint]
    [(epsilonRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint]
    [(aRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u + 1} (epsilonRingedHom X))
      (ModuleQis.{u + 1} (overFppfRingedSite X))] :
    IsIso (piPullbackDerivedUnit ((moduleCarrierLiftDerived X).obj K.obj)) :=
  sorry

/-- For `K` in `D_QCoh(𝒪_X)`, the map `K ⟶ Ra_{X,*}(La_X^* K)` is an
isomorphism. -/
theorem aDerivedUnit_isIso {X : AlgebraicSpace S} (K : DerivedQCoh X)
    [(aRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u + 1} (aRingedHom X))
      (ModuleQis.{u + 1} (overFppfRingedSite X))] :
    IsIso (aDerivedUnit ((moduleCarrierLiftDerived X).obj K.obj)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.AssociatedModule

end

end
