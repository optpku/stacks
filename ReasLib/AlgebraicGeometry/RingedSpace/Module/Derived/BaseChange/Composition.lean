/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.BaseChange
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback.Composition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.Composition
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Vertical composition of unbounded ringed-space base-change maps

This leaf owns the outer-rectangle comparison and the composite of two objectwise mate maps.
The comparison isomorphisms and adjunctions are explicit inputs, so the data layer does not select
inverses from unfinished proof fields.
-/

open AlgebraicGeometry CategoryTheory
open scoped RingedSpace.Hom RingedSpaceDerivedPullback RingedSpaceDerivedPushforward

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom.DerivedBaseChange.Composition

variable {X' X Y' Y Z' Z : RingedSpace.{u}}

/-- The derived-pullback square for a vertically pasted pair of base-change squares. -/
@[stacks 0ATL "outer derived base-change square"]
noncomputable abbrev squareIso
    {k : X' ⟶ X} {f' : X' ⟶ Y'} {l : Y' ⟶ Y} {f : X ⟶ Y}
    {m : Z' ⟶ Z} {g' : Y' ⟶ Z'} {g : Y ⟶ Z}
    (top : L(l)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(k)^*)
    (bottom : L(m)^* ⋙ L(g')^* ≅ L(g)^* ⋙ L(l)^*)
    (left : L(g')^* ⋙ L(f')^* ≅ modulePullbackDerived (f' ≫ g'))
    (right : L(g)^* ⋙ L(f)^* ≅ modulePullbackDerived (f ≫ g)) :
    L(m)^* ⋙ modulePullbackDerived (f' ≫ g') ≅
      modulePullbackDerived (f ≫ g) ⋙ L(k)^* :=
  Functor.isoWhiskerLeft (L(m)^*) left.symm ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerRight bottom (L(f')^*) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (L(g)^*) top ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight right (L(k)^*)

/-- The derived-pushforward comparison induced by chosen adjunctions and a pullback comparison. -/
@[stacks 0ATL "derived pushforward composition comparison"]
noncomputable abbrev pushforwardIso
    {f : X ⟶ Y} {g : Y ⟶ Z}
    (adj_f : L(f)^* ⊣ R(f)_*) (adj_g : L(g)^* ⊣ R(g)_*)
    (adj_fg : modulePullbackDerived (f ≫ g) ⊣ moduleDerivedPushforward (f ≫ g))
    (pull : L(g)^* ⋙ L(f)^* ≅ modulePullbackDerived (f ≫ g)) :
    R(f)_* ⋙ R(g)_* ≅ moduleDerivedPushforward (f ≫ g) :=
  ((adj_g.comp adj_f).ofNatIsoLeft pull).rightAdjointUniq adj_fg

/-- The objectwise composite of two unbounded base-change components. -/
@[stacks 0ATL "vertical composite of unbounded base-change components"]
noncomputable def map
    {k : X' ⟶ X} {f' : X' ⟶ Y'} {l : Y' ⟶ Y} {f : X ⟶ Y}
    {m : Z' ⟶ Z} {g' : Y' ⟶ Z'} {g : Y ⟶ Z}
    (pull_fg : L(g)^* ⋙ L(f)^* ≅ modulePullbackDerived (f ≫ g))
    (pull_f'g' : L(g')^* ⋙ L(f')^* ≅ modulePullbackDerived (f' ≫ g'))
    (adj_f : L(f)^* ⊣ R(f)_*) (adj_g : L(g)^* ⊣ R(g)_*)
    (adj_fg : modulePullbackDerived (f ≫ g) ⊣ moduleDerivedPushforward (f ≫ g))
    (adj_f' : L(f')^* ⊣ R(f')_*) (adj_g' : L(g')^* ⊣ R(g')_*)
    (adj_f'g' : modulePullbackDerived (f' ≫ g') ⊣
      moduleDerivedPushforward (f' ≫ g'))
    (K : DerivedCategory X.Modules)
    (η_top : (source f l).obj K ⟶ (target k f').obj K)
    (η_bottom : (source g m).obj ((R(f)_*).obj K) ⟶
      (target l g').obj ((R(f)_*).obj K)) :
    (source (f ≫ g) m).obj K ⟶ (target k (f' ≫ g')).obj K :=
  (Functor.isoWhiskerRight (pushforwardIso adj_f adj_g adj_fg pull_fg)
      (L(m)^*)).inv.app K ≫
    η_bottom ≫
    (R(g')_*).map η_top ≫
    (pushforwardIso adj_f' adj_g' adj_f'g' pull_f'g').hom.app ((L(k)^*).obj K)

/-- Remark 20.28.4 (0ATL): vertical composition preserves the objectwise base-change mate
equation. -/
@[stacks 0ATL "vertical composition preserves base-change mates"]
theorem map_isMapAt
    {k : X' ⟶ X} {f' : X' ⟶ Y'} {l : Y' ⟶ Y} {f : X ⟶ Y}
    {m : Z' ⟶ Z} {g' : Y' ⟶ Z'} {g : Y ⟶ Z}
    (pull_top : L(l)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(k)^*)
    (pull_bottom : L(m)^* ⋙ L(g')^* ≅ L(g)^* ⋙ L(l)^*)
    (pull_fg : L(g)^* ⋙ L(f)^* ≅ modulePullbackDerived (f ≫ g))
    (pull_f'g' : L(g')^* ⋙ L(f')^* ≅ modulePullbackDerived (f' ≫ g'))
    (adj_f : L(f)^* ⊣ R(f)_*) (adj_f' : L(f')^* ⊣ R(f')_*)
    (adj_g : L(g)^* ⊣ R(g)_*) (adj_g' : L(g')^* ⊣ R(g')_*)
    (adj_fg : modulePullbackDerived (f ≫ g) ⊣ moduleDerivedPushforward (f ≫ g))
    (adj_f'g' : modulePullbackDerived (f' ≫ g') ⊣
      moduleDerivedPushforward (f' ≫ g'))
    (K : DerivedCategory X.Modules)
    (η_top : (source f l).obj K ⟶ (target k f').obj K)
    (η_bottom : (source g m).obj ((R(f)_*).obj K) ⟶
      (target l g').obj ((R(f)_*).obj K))
    (h_top : IsMapAt adj_f adj_f' pull_top K η_top)
    (h_bottom : IsMapAt adj_g adj_g' pull_bottom ((R(f)_*).obj K) η_bottom) :
    IsMapAt adj_fg adj_f'g'
      (squareIso pull_top pull_bottom pull_f'g' pull_fg) K
      (map pull_fg pull_f'g' adj_f adj_g adj_fg adj_f' adj_g' adj_f'g' K η_top η_bottom) := sorry

/-- Canonical base-change components compose to the canonical outer component. -/
@[stacks 0ATL "canonical vertical base-change composition"]
theorem map_eq
    {k : X' ⟶ X} {f' : X' ⟶ Y'} {l : Y' ⟶ Y} {f : X ⟶ Y}
    {m : Z' ⟶ Z} {g' : Y' ⟶ Z'} {g : Y ⟶ Z}
    (pull_top : L(l)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(k)^*)
    (pull_bottom : L(m)^* ⋙ L(g')^* ≅ L(g)^* ⋙ L(l)^*)
    (pull_fg : L(g)^* ⋙ L(f)^* ≅ modulePullbackDerived (f ≫ g))
    (pull_f'g' : L(g')^* ⋙ L(f')^* ≅ modulePullbackDerived (f' ≫ g'))
    (adj_f : L(f)^* ⊣ R(f)_*) (adj_f' : L(f')^* ⊣ R(f')_*)
    (adj_g : L(g)^* ⊣ R(g)_*) (adj_g' : L(g')^* ⊣ R(g')_*)
    (adj_fg : modulePullbackDerived (f ≫ g) ⊣ moduleDerivedPushforward (f ≫ g))
    (adj_f'g' : modulePullbackDerived (f' ≫ g') ⊣
      moduleDerivedPushforward (f' ≫ g'))
    (K : DerivedCategory X.Modules) :
    map pull_fg pull_f'g' adj_f adj_g adj_fg adj_f' adj_g' adj_f'g' K
        (DerivedBaseChange.app adj_f adj_f' pull_top K)
        (DerivedBaseChange.app adj_g adj_g' pull_bottom ((R(f)_*).obj K)) =
      DerivedBaseChange.app adj_fg adj_f'g'
        (squareIso pull_top pull_bottom pull_f'g' pull_fg) K := sorry

end AlgebraicGeometry.RingedSpace.Hom.DerivedBaseChange.Composition
