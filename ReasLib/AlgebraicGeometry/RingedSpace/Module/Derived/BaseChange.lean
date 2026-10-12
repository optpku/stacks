/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback.Composition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward
public import ReasLib.CategoryTheory.Adjunction.BaseChange
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Unbounded base change for modules on ringed spaces

This leaf presents the unbounded base-change mate for a commutative square of ringed spaces.
The square of derived pullbacks and the two derived adjunctions are explicit inputs, so the
construction remains reusable before geometric comparison-isomorphism proofs are completed.
-/

open AlgebraicGeometry CategoryTheory
open scoped RingedSpace.Hom RingedSpaceDerivedPullback RingedSpaceDerivedPushforward

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom.DerivedBaseChange

/-- The source functor `R(f)_* ⋙ L(g)^*` of unbounded base change. -/
@[stacks 02N8 "unbounded derived base-change source"]
abbrev source {X S S' : RingedSpace.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) :
    DerivedCategory X.Modules ⥤ DerivedCategory S'.Modules :=
  R(f)_* ⋙ L(g)^*

/-- The target functor `L(g')^* ⋙ R(f')_*` of unbounded base change. -/
@[stacks 02N8 "unbounded derived base-change target"]
abbrev target {X X' S' : RingedSpace.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') :
    DerivedCategory X.Modules ⥤ DerivedCategory S'.Modules :=
  L(g')^* ⋙ R(f')_*

/-- The derived pullback square obtained from explicit composition isomorphisms. -/
@[stacks 02N8 "unbounded derived pullback square from composition isomorphisms"]
noncomputable def pullbackIsoOfCompIso
    {X X' S S' : RingedSpace.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (sq : CommSq g' f' f g)
    (left : L(g)^* ⋙ L(f')^* ≅ modulePullbackDerived (f' ≫ g))
    (right : L(f)^* ⋙ L(g')^* ≅ modulePullbackDerived (g' ≫ f)) :
    L(g)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(g')^* :=
  left ≪≫
    eqToIso (congrArg
      (fun h : X' ⟶ S => AlgebraicGeometry.RingedSpace.modulePullbackDerived h)
      sq.w.symm) ≪≫
    right.symm

/-- The derived pullback square obtained from explicit invertibility certificates for the two
composition comparisons. -/
@[stacks 02N8 "unbounded derived pullback square"]
noncomputable def pullbackIsoOfIsIso
    {X X' S S' : RingedSpace.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (sq : CommSq g' f' f g)
    (hleft : IsIso (modulePullbackDerived.compComparison f' g))
    (hright : IsIso (modulePullbackDerived.compComparison g' f)) :
    L(g)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(g')^* :=
  pullbackIsoOfCompIso sq
    (modulePullbackDerived.compIso f' g hleft)
    (modulePullbackDerived.compIso g' f hright)

/-- The unbounded derived base-change transformation for explicit derived adjunctions and a
derived pullback square. -/
@[stacks 02N8 "unbounded derived base-change transformation"]
noncomputable def map
    {X X' S S' : RingedSpace.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (adj_f : L(f)^* ⊣ R(f)_*)
    (adj_f' : L(f')^* ⊣ R(f')_*)
    (squareIso : L(g)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(g')^*) :
    source f g ⟶ target g' f' :=
  CategoryTheory.DerivedBaseChange.map adj_f adj_f' squareIso

/-- The component of the unbounded derived base-change transformation at `K`. -/
@[stacks 02N8 "unbounded derived base-change component"]
noncomputable abbrev app
    {X X' S S' : RingedSpace.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (adj_f : L(f)^* ⊣ R(f)_*)
    (adj_f' : L(f')^* ⊣ R(f')_*)
    (squareIso : L(g)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(g')^*)
    (K : DerivedCategory X.Modules) :
    (source f g).obj K ⟶ (target g' f').obj K :=
  (map adj_f adj_f' squareIso).app K

/-- The objectwise specification for an unbounded ringed-space base-change component. -/
@[stacks 02N8 "unbounded derived base-change component specification"]
abbrev IsMapAt
    {X X' S S' : RingedSpace.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (adj_f : L(f)^* ⊣ R(f)_*)
    (adj_f' : L(f')^* ⊣ R(f')_*)
    (squareIso : L(g)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(g')^*)
    (K : DerivedCategory X.Modules)
    (η : (source f g).obj K ⟶ (target g' f').obj K) : Prop :=
  CategoryTheory.DerivedBaseChange.IsMapAt adj_f adj_f' squareIso K η

/-- The canonical unbounded ringed-space base-change component satisfies its mate equation. -/
@[stacks 02N8 "unbounded derived base-change component specification"]
theorem map_isMapAt
    {X X' S S' : RingedSpace.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (adj_f : L(f)^* ⊣ R(f)_*)
    (adj_f' : L(f')^* ⊣ R(f')_*)
    (squareIso : L(g)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(g')^*)
    (K : DerivedCategory X.Modules) :
    IsMapAt adj_f adj_f' squareIso K (app adj_f adj_f' squareIso K) := sorry

/-- The component is characterized by the adjunction-transpose formula. -/
@[stacks 02N8 "unbounded derived base-change component specification"]
theorem map_spec
    {X X' S S' : RingedSpace.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (adj_f : L(f)^* ⊣ R(f)_*)
    (adj_f' : L(f')^* ⊣ R(f')_*)
    (squareIso : L(g)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(g')^*)
    (K : DerivedCategory X.Modules) :
    ((adj_f'.homEquiv ((L(g)^*).obj ((R(f)_*).obj K)) ((L(g')^*).obj K)).symm
        (app adj_f adj_f' squareIso K)) =
      squareIso.hom.app ((R(f)_*).obj K) ≫ (L(g')^*).map (adj_f.counit.app K) := sorry

/-- A component satisfying the unbounded mate equation is the canonical component. -/
@[stacks 02N8 "uniqueness of unbounded derived base-change components"]
theorem IsMapAt.eq_app
    {X X' S S' : RingedSpace.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (adj_f : L(f)^* ⊣ R(f)_*)
    (adj_f' : L(f')^* ⊣ R(f')_*)
    (squareIso : L(g)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(g')^*)
    {K : DerivedCategory X.Modules}
    {η : (source f g).obj K ⟶ (target g' f').obj K}
    (hη : IsMapAt adj_f adj_f' squareIso K η) :
    η = app adj_f adj_f' squareIso K := sorry

/-- The natural-transformation specification for unbounded ringed-space base change. -/
@[stacks 02N8 "unbounded derived base-change specification"]
abbrev IsMap
    {X X' S S' : RingedSpace.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (adj_f : L(f)^* ⊣ R(f)_*)
    (adj_f' : L(f')^* ⊣ R(f')_*)
    (squareIso : L(g)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(g')^*)
    (η : source f g ⟶ target g' f') : Prop :=
  CategoryTheory.DerivedBaseChange.IsMap adj_f adj_f' squareIso η

/-- The canonical unbounded ringed-space base-change transformation satisfies its specification. -/
@[stacks 02N8 "unbounded derived base-change specification"]
theorem map_isMap
    {X X' S S' : RingedSpace.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (adj_f : L(f)^* ⊣ R(f)_*)
    (adj_f' : L(f')^* ⊣ R(f')_*)
    (squareIso : L(g)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(g')^*) :
    IsMap adj_f adj_f' squareIso (map adj_f adj_f' squareIso) := sorry

/-- A natural transformation satisfying the unbounded mate equation is the canonical map. -/
@[stacks 02N8 "uniqueness of unbounded derived base-change maps"]
theorem IsMap.eq_map
    {X X' S S' : RingedSpace.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (adj_f : L(f)^* ⊣ R(f)_*)
    (adj_f' : L(f')^* ⊣ R(f')_*)
    (squareIso : L(g)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(g')^*)
    {η : source f g ⟶ target g' f'}
    (hη : IsMap adj_f adj_f' squareIso η) :
    η = map adj_f adj_f' squareIso := sorry

end AlgebraicGeometry.RingedSpace.Hom.DerivedBaseChange

namespace AlgebraicGeometry.RingedSpace

open Hom.DerivedBaseChange

variable {X X' S S' : RingedSpace.{u}}

/-- Compatibility view of the source object used by Remark 20.28.3. -/
@[stacks 08HY "unbounded derived base-change source object"]
abbrev derivedBaseChangeSource
    (f : X ⟶ S) (g : S' ⟶ S) (K : DerivedCategory X.Modules) :
    DerivedCategory S'.Modules :=
  (Hom.DerivedBaseChange.source f g).obj K

/-- Compatibility view of the target object used by Remark 20.28.3. -/
@[stacks 08HY "unbounded derived base-change target object"]
abbrev derivedBaseChangeTarget
    (g' : X' ⟶ X) (f' : X' ⟶ S') (K : DerivedCategory X.Modules) :
    DerivedCategory S'.Modules :=
  (Hom.DerivedBaseChange.target g' f').obj K

/-- The adjoint-side composite underlying the unbounded base-change map. -/
@[stacks 08HY "unbounded derived base-change mate composite"]
noncomputable def unboundedDerivedBaseChangeMapAdjoint
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (adjf : L(f)^* ⊣ R(f)_*)
    (hpull : L(g)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(g')^*)
    (K : DerivedCategory X.Modules) :
    (L(f')^*).obj (derivedBaseChangeSource f g K) ⟶ (L(g')^*).obj K :=
  hpull.hom.app ((R(f)_*).obj K) ≫
    (L(g')^*).map (adjf.counit.app K)

/-- Compatibility predicate for an objectwise unbounded base-change component. -/
@[stacks 08HY "unbounded derived base-change compatibility predicate"]
abbrev IsUnboundedDerivedBaseChangeMap
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (adjf : L(f)^* ⊣ R(f)_*)
    (adjf' : L(f')^* ⊣ R(f')_*)
    (hpull : L(g)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(g')^*)
    (K : DerivedCategory X.Modules)
    (τ : derivedBaseChangeSource f g K ⟶ derivedBaseChangeTarget g' f' K) : Prop :=
  Hom.DerivedBaseChange.IsMapAt adjf adjf' hpull K τ

/-- Compatibility spelling of the canonical unbounded derived base-change component. -/
@[stacks 08HY "unbounded derived base-change map"]
noncomputable abbrev unboundedDerivedBaseChangeMap
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (adjf : L(f)^* ⊣ R(f)_*)
    (adjf' : L(f')^* ⊣ R(f')_*)
    (hpull : L(g)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(g')^*)
    (K : DerivedCategory X.Modules) :
    derivedBaseChangeSource f g K ⟶ derivedBaseChangeTarget g' f' K :=
  Hom.DerivedBaseChange.app adjf adjf' hpull K

/-- The canonical compatibility statement for the unbounded base-change component. -/
@[stacks 08HY "unbounded derived base-change map specification"]
theorem unboundedDerivedBaseChangeMap_spec
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (adjf : L(f)^* ⊣ R(f)_*)
    (adjf' : L(f')^* ⊣ R(f')_*)
    (hpull : L(g)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(g')^*)
    (K : DerivedCategory X.Modules) :
    IsUnboundedDerivedBaseChangeMap g' f' f g adjf adjf' hpull K
      (unboundedDerivedBaseChangeMap g' f' f g adjf adjf' hpull K) := sorry

/-- A compatible unbounded base-change component is uniquely determined. -/
@[stacks 08HY "uniqueness of unbounded derived base-change maps"]
theorem eq_unboundedDerivedBaseChangeMap
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (adjf : L(f)^* ⊣ R(f)_*)
    (adjf' : L(f')^* ⊣ R(f')_*)
    (hpull : L(g)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(g')^*)
    (K : DerivedCategory X.Modules)
    (τ : derivedBaseChangeSource f g K ⟶ derivedBaseChangeTarget g' f' K)
    (hτ : IsUnboundedDerivedBaseChangeMap g' f' f g adjf adjf' hpull K τ) :
    τ = unboundedDerivedBaseChangeMap g' f' f g adjf adjf' hpull K := sorry

end AlgebraicGeometry.RingedSpace
