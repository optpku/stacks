/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.BaseChange
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.Composition

@[expose] public section

/-!
# Vertical composition of derived base-change maps

For two vertically composable squares of ringed-site morphisms, this module constructs the
derived-pullback square for the outer rectangle and the corresponding composite of base-change
maps. The mate equation is stable under this composition.
-/

open CategoryTheory
open ComplexShape

noncomputable section

universe z u v w

namespace RingedSite.Hom.DerivedBaseChange.Composition

section

variable {B' B C' C D' D : RingedSite.{u, v, w}}
variable (k : RingedSite.Hom B' B) (f' : RingedSite.Hom B' C')
variable (f : RingedSite.Hom B C) (l : RingedSite.Hom C' C)
variable (g' : RingedSite.Hom C' D') (g : RingedSite.Hom C D)
variable (m : RingedSite.Hom D' D)
variable [UnivLE.{max u v, z}]
variable [(k.modulePushforward.{z}).IsRightAdjoint]
variable [(f'.modulePushforward.{z}).IsRightAdjoint]
variable [(f.modulePushforward.{z}).IsRightAdjoint]
variable [(l.modulePushforward.{z}).IsRightAdjoint]
variable [(g'.modulePushforward.{z}).IsRightAdjoint]
variable [(g.modulePushforward.{z}).IsRightAdjoint]
variable [(m.modulePushforward.{z}).IsRightAdjoint]
variable [((f'.comp g').modulePushforward.{z}).IsRightAdjoint]
variable [((f.comp g).modulePushforward.{z}).IsRightAdjoint]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{z} f) (ModuleQis.{z} B)]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{z} f') (ModuleQis.{z} B')]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{z} g) (ModuleQis.{z} C)]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{z} g') (ModuleQis.{z} C')]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{z} (f.comp g)) (ModuleQis.{z} B)]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{z} (f'.comp g')) (ModuleQis.{z} B')]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{z} k) (ModuleQis.{z} B)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{z} f') (ModuleQis.{z} C')]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{z} f) (ModuleQis.{z} C)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{z} l) (ModuleQis.{z} C)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{z} g') (ModuleQis.{z} D')]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{z} g) (ModuleQis.{z} D)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{z} m) (ModuleQis.{z} D)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{z} (f.comp g)) (ModuleQis.{z} D)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{z} (f'.comp g')) (ModuleQis.{z} D')]
variable [DerivedAdjunction.HasPair.{z} f]
variable [DerivedAdjunction.HasPair.{z} f']
variable [DerivedAdjunction.HasPair.{z} g]
variable [DerivedAdjunction.HasPair.{z} g']
variable [DerivedAdjunction.HasPair.{z} (f.comp g)]
variable [DerivedAdjunction.HasPair.{z} (f'.comp g')]

/-- The derived-pullback comparison for the outer rectangle obtained by pasting two vertically
composable squares and the pullback-composition isomorphisms on their vertical sides. -/
@[stacks 0E46 "outer derived-pullback square"]
noncomputable abbrev squareIso
    (top : modulePullbackDerived.{z} l ⋙ modulePullbackDerived.{z} f' ≅
      modulePullbackDerived.{z} f ⋙ modulePullbackDerived.{z} k)
    (bottom : modulePullbackDerived.{z} m ⋙ modulePullbackDerived.{z} g' ≅
      modulePullbackDerived.{z} g ⋙ modulePullbackDerived.{z} l)
    (left : modulePullbackDerived.{z} g' ⋙ modulePullbackDerived.{z} f' ≅
      modulePullbackDerived.{z} (f'.comp g'))
    (right : modulePullbackDerived.{z} g ⋙ modulePullbackDerived.{z} f ≅
      modulePullbackDerived.{z} (f.comp g)) :
    modulePullbackDerived.{z} m ⋙ modulePullbackDerived.{z} (f'.comp g') ≅
      modulePullbackDerived.{z} (f.comp g) ⋙ modulePullbackDerived.{z} k :=
  Functor.isoWhiskerLeft (modulePullbackDerived.{z} m) left.symm ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerRight bottom (modulePullbackDerived.{z} f') ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (modulePullbackDerived.{z} g) top ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight right (modulePullbackDerived.{z} k)

/-- The composite of base-change maps for two vertically composable squares, transported across
the chosen derived-pushforward composition isomorphisms. -/
@[stacks 0E46 "composite unbounded base-change morphism"]
noncomputable def map
    (left : modulePullbackDerived.{z} g' ⋙ modulePullbackDerived.{z} f' ≅
      modulePullbackDerived.{z} (f'.comp g'))
    (right : modulePullbackDerived.{z} g ⋙ modulePullbackDerived.{z} f ≅
      modulePullbackDerived.{z} (f.comp g))
    (K : ModuleDerived.{z} B)
    (η_top : (modulePullbackDerived.{z} l).obj
        ((modulePushforwardDerived.{z} f).obj K) ⟶
      (modulePushforwardDerived.{z} f').obj
        ((modulePullbackDerived.{z} k).obj K))
    (η_bottom : (modulePullbackDerived.{z} m).obj
        ((modulePushforwardDerived.{z} g).obj
          ((modulePushforwardDerived.{z} f).obj K)) ⟶
      (modulePushforwardDerived.{z} g').obj
        ((modulePullbackDerived.{z} l).obj
          ((modulePushforwardDerived.{z} f).obj K))) :
    (modulePullbackDerived.{z} m).obj
        ((modulePushforwardDerived.{z} (f.comp g)).obj K) ⟶
      (modulePushforwardDerived.{z} (f'.comp g')).obj
        ((modulePullbackDerived.{z} k).obj K) :=
  (Functor.isoWhiskerRight
      (modulePushforwardDerivedCompIsoOfPullback f g right)
      (modulePullbackDerived.{z} m)).inv.app K ≫
    η_bottom ≫
    (modulePushforwardDerived.{z} g').map η_top ≫
    (Functor.isoWhiskerLeft (modulePullbackDerived.{z} k)
      (modulePushforwardDerivedCompIsoOfPullback f' g' left)).hom.app K

/-- Vertical composition preserves the defining mate equation for derived base-change maps. -/
@[stacks 0E46 "vertical composition of unbounded base-change maps"]
theorem map_isMap
    (top : modulePullbackDerived.{z} l ⋙ modulePullbackDerived.{z} f' ≅
      modulePullbackDerived.{z} f ⋙ modulePullbackDerived.{z} k)
    (bottom : modulePullbackDerived.{z} m ⋙ modulePullbackDerived.{z} g' ≅
      modulePullbackDerived.{z} g ⋙ modulePullbackDerived.{z} l)
    (left : modulePullbackDerived.{z} g' ⋙ modulePullbackDerived.{z} f' ≅
      modulePullbackDerived.{z} (f'.comp g'))
    (right : modulePullbackDerived.{z} g ⋙ modulePullbackDerived.{z} f ≅
      modulePullbackDerived.{z} (f.comp g))
    (K : ModuleDerived.{z} B)
    (η_top : (modulePullbackDerived.{z} l).obj
        ((modulePushforwardDerived.{z} f).obj K) ⟶
      (modulePushforwardDerived.{z} f').obj
        ((modulePullbackDerived.{z} k).obj K))
    (η_bottom : (modulePullbackDerived.{z} m).obj
        ((modulePushforwardDerived.{z} g).obj
          ((modulePushforwardDerived.{z} f).obj K)) ⟶
      (modulePushforwardDerived.{z} g').obj
        ((modulePullbackDerived.{z} l).obj
          ((modulePushforwardDerived.{z} f).obj K)))
    (h_top : DerivedBaseChange.IsMap k f' f l top K η_top)
    (h_bottom : DerivedBaseChange.IsMap l g' g m bottom
      ((modulePushforwardDerived.{z} f).obj K) η_bottom) :
    DerivedBaseChange.IsMap k (f'.comp g') (f.comp g) m
      (squareIso k f' f l g' g m top bottom left right) K
      (map k f' f l g' g m left right K η_top η_bottom) := sorry

/-- The composite of the two canonical derived base-change maps is the canonical base-change map
for the outer rectangle. -/
@[stacks 0E46 "canonical unbounded base-change maps compose"]
theorem map_eq
    (top : modulePullbackDerived.{z} l ⋙ modulePullbackDerived.{z} f' ≅
      modulePullbackDerived.{z} f ⋙ modulePullbackDerived.{z} k)
    (bottom : modulePullbackDerived.{z} m ⋙ modulePullbackDerived.{z} g' ≅
      modulePullbackDerived.{z} g ⋙ modulePullbackDerived.{z} l)
    (left : modulePullbackDerived.{z} g' ⋙ modulePullbackDerived.{z} f' ≅
      modulePullbackDerived.{z} (f'.comp g'))
    (right : modulePullbackDerived.{z} g ⋙ modulePullbackDerived.{z} f ≅
      modulePullbackDerived.{z} (f.comp g))
    (K : ModuleDerived.{z} B) :
    map k f' f l g' g m left right K
        (DerivedBaseChange.map k f' f l top K)
        (DerivedBaseChange.map l g' g m bottom
          ((modulePushforwardDerived.{z} f).obj K)) =
      DerivedBaseChange.map k (f'.comp g') (f.comp g) m
        (squareIso k f' f l g' g m top bottom left right) K := sorry

end

end RingedSite.Hom.DerivedBaseChange.Composition

-- Both data declarations are assembled from explicit square and adjunction-composition
-- isomorphisms; their construction does not consume either theorem below.
