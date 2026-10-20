module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Adjunction
public import ReasLib.CategoryTheory.Adjunction.BaseChange

@[expose] public section

/-!
# Base change for derived module functors on ringed sites

This module specializes the categorical mate construction to the canonical total-derived
pullback-pushforward adjunctions on ringed sites. The square of derived pullbacks remains explicit;
the resulting base-change morphism and its characterization are canonical.
-/

open CategoryTheory
open ComplexShape

noncomputable section

universe z uX' vX' uX vX uY' vY' uY vY w

namespace RingedSite.Hom.DerivedBaseChange

variable {X' : RingedSite.{uX', vX', w}} {X : RingedSite.{uX, vX, w}}
variable {Y' : RingedSite.{uY', vY', w}} {Y : RingedSite.{uY, vY, w}}
variable (g' : RingedSite.Hom X' X) (f' : RingedSite.Hom X' Y')
variable (f : RingedSite.Hom X Y) (g : RingedSite.Hom Y' Y)
variable [UnivLE.{max uX' vX', z}] [UnivLE.{max uX vX, z}]
variable [UnivLE.{max uY' vY', z}] [UnivLE.{max uY vY, z}]
variable [(g'.modulePushforward.{z}).IsRightAdjoint]
variable [(f'.modulePushforward.{z}).IsRightAdjoint]
variable [(f.modulePushforward.{z}).IsRightAdjoint]
variable [(g.modulePushforward.{z}).IsRightAdjoint]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{z} f) (ModuleQis.{z} X)]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{z} f') (ModuleQis.{z} X')]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{z} g) (ModuleQis.{z} Y)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{z} g') (ModuleQis.{z} X)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{z} f) (ModuleQis.{z} Y)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{z} f') (ModuleQis.{z} Y')]
variable [DerivedAdjunction.HasPair.{z} f]
variable [DerivedAdjunction.HasPair.{z} f']
variable (squareIso :
  modulePullbackDerived.{z} g ⋙ modulePullbackDerived.{z} f' ≅
    modulePullbackDerived.{z} f ⋙ modulePullbackDerived.{z} g')
variable (K : ModuleDerived.{z} X)

/-- The source functor `R(f)_* ⋙ L(g)^*` of unbounded ringed-site base change. -/
@[stacks 0FN7 "unbounded derived ringed-site base-change source"]
abbrev source :
    ModuleDerived.{z} X ⥤ ModuleDerived.{z} Y' :=
  modulePushforwardDerived.{z} f ⋙ modulePullbackDerived.{z} g

/-- The target functor `L(g')^* ⋙ R(f')_*` of unbounded ringed-site base change. -/
@[stacks 0FN7 "unbounded derived ringed-site base-change target"]
abbrev target :
    ModuleDerived.{z} X ⥤ ModuleDerived.{z} Y' :=
  modulePullbackDerived.{z} g' ⋙ modulePushforwardDerived.{z} f'

/-- The natural transformation obtained by taking the mate of the derived pullback square. -/
@[stacks 0FN7 "unbounded derived ringed-site base-change natural transformation"]
noncomputable abbrev mapNatTrans :
    source f g ⟶ target g' f' :=
  CategoryTheory.DerivedBaseChange.map
    (moduleDerivedAdjunction.{z} f)
    (moduleDerivedAdjunction.{z} f')
    squareIso

/-- The component of the unbounded ringed-site base-change natural transformation. -/
@[stacks 0FN7 "unbounded derived ringed-site base-change component"]
noncomputable abbrev mapNatTrans_app :
    (source f g).obj K ⟶ (target g' f').obj K :=
  (mapNatTrans g' f' f g squareIso).app K

/-- The functor-level mate specification for a ringed-site base-change transformation. -/
@[stacks 0FN7 "unbounded derived ringed-site base-change specification"]
abbrev IsMapNatTrans (η : source f g ⟶ target g' f') : Prop :=
  CategoryTheory.DerivedBaseChange.IsMap
    (moduleDerivedAdjunction.{z} f)
    (moduleDerivedAdjunction.{z} f')
    squareIso η

/-- The canonical ringed-site base-change natural transformation satisfies its mate specification. -/
@[stacks 0FN7 "unbounded derived ringed-site base-change specification"]
theorem mapNatTrans_isMap :
    IsMapNatTrans g' f' f g squareIso (mapNatTrans g' f' f g squareIso) := sorry

/-- A morphism is the derived base-change map for a square of ringed-site morphisms when it
satisfies the defining adjunction-mate equation. -/
@[stacks 07A7 "unbounded derived base-change predicate"]
abbrev IsMap
    (η : (modulePullbackDerived.{z} g).obj
        ((modulePushforwardDerived.{z} f).obj K) ⟶
      (modulePushforwardDerived.{z} f').obj
        ((modulePullbackDerived.{z} g').obj K)) : Prop :=
  IsDerivedBaseChangeMap
    (modulePullbackDerived.{z} f) (modulePullbackDerived.{z} f')
    (modulePullbackDerived.{z} g) (modulePullbackDerived.{z} g')
    (modulePushforwardDerived.{z} f) (modulePushforwardDerived.{z} f')
    (moduleDerivedAdjunction.{z} f) (moduleDerivedAdjunction.{z} f')
    squareIso K η

/-- Remark 21.19.3 (07A7): the canonical unbounded derived base-change morphism associated to a
square of ringed-site morphisms. -/
@[stacks 07A7 "unbounded derived base-change morphism"]
noncomputable abbrev map :
    (modulePullbackDerived.{z} g).obj
        ((modulePushforwardDerived.{z} f).obj K) ⟶
      (modulePushforwardDerived.{z} f').obj
        ((modulePullbackDerived.{z} g').obj K) :=
  derivedBaseChangeMap
    (modulePullbackDerived.{z} f) (modulePullbackDerived.{z} f')
    (modulePullbackDerived.{z} g) (modulePullbackDerived.{z} g')
    (modulePushforwardDerived.{z} f) (modulePushforwardDerived.{z} f')
    (moduleDerivedAdjunction.{z} f) (moduleDerivedAdjunction.{z} f')
    squareIso K

/-- The functor-level transformation and the existing objectwise map are the same mate. -/
@[stacks 0FN7 "unbounded derived ringed-site base-change component bridge"]
theorem mapNatTrans_app_eq_map :
    mapNatTrans_app g' f' f g squareIso K = map g' f' f g squareIso K := sorry

/-- The canonical derived base-change morphism satisfies its defining mate equation. -/
@[stacks 07A7 "unbounded derived base-change morphism specification"]
theorem map_isMap :
    IsMap g' f' f g squareIso K (map g' f' f g squareIso K) := sorry

/-- Transposing the canonical derived base-change morphism recovers the square comparison
followed by the pullback of the counit. -/
theorem map_spec :
    ((moduleDerivedAdjunction.{z} f').homEquiv
        ((modulePullbackDerived.{z} g).obj
          ((modulePushforwardDerived.{z} f).obj K))
        ((modulePullbackDerived.{z} g').obj K)).symm
        (map g' f' f g squareIso K) =
      squareIso.hom.app ((modulePushforwardDerived.{z} f).obj K) ≫
        (modulePullbackDerived.{z} g').map
          ((moduleDerivedAdjunction.{z} f).counit.app K) := sorry

/-- A morphism satisfying the derived base-change mate equation equals the canonical map. -/
theorem IsMap.eq_map
    {η : (modulePullbackDerived.{z} g).obj
        ((modulePushforwardDerived.{z} f).obj K) ⟶
      (modulePushforwardDerived.{z} f').obj
        ((modulePullbackDerived.{z} g').obj K)}
    (hη : IsMap g' f' f g squareIso K η) :
    η = map g' f' f g squareIso K := sorry

end RingedSite.Hom.DerivedBaseChange

-- The base-change morphism is Mathlib's concrete mate of `squareIso`; no theorem proof is used
-- to choose its data.
