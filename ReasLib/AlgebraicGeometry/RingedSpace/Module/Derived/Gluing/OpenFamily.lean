/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace
public import ReasLib.CategoryTheory.DerivedCategory.Ext
import Mathlib.Tactic.CrossRefAttribute

/-!
# Gluing data on a family of opens

An `OpenFamily` records local derived modules and coherent restriction isomorphisms.  A
`Realization` bundles the local identifications of one ambient object with their compatibility
law, while `Realizes` is the proposition that such data exists.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.Gluing

open OpenSubspace.Restriction

/-- Situation 20.45.3: coherent derived-module gluing data indexed by a family of opens. -/
@[stacks 0D67 "derived gluing data on an open family"]
structure OpenFamily (X : RingedSpace.{u}) (𝓑 : Set (Opens X.carrier)) where
  /-- The local derived module attached to an open in the family. -/
  obj (U : Opens X.carrier) (hU : U ∈ 𝓑) : moduleDerivedOnOpen X U
  /-- Restriction from a larger family member to a smaller one. -/
  ρ (U V : Opens X.carrier) (hU : U ∈ 𝓑) (hV : V ∈ 𝓑) (hVU : V ≤ U) :
    (derivedBetween X hVU).obj (obj U hU) ≅ obj V hV
  /-- Restriction isomorphisms compose along a chain of inclusions. -/
  ρ_comp (U V W : Opens X.carrier)
      (hU : U ∈ 𝓑) (hV : V ∈ 𝓑) (hW : W ∈ 𝓑) (hWV : W ≤ V) (hVU : V ≤ U) :
    ((derivedBetweenCompIso X hWV hVU).app (obj U hU)) ≪≫
        ρ U W hU hW (hWV.trans hVU) =
      (derivedBetween X hWV).mapIso (ρ U V hU hV hVU) ≪≫
        ρ V W hV hW hWV

namespace OpenFamily

variable {X : RingedSpace.{u}} {𝓑 : Set (Opens X.carrier)}

/-- Negative self-Ext groups of every local object vanish. -/
@[stacks 0D67 "negative local self-Ext vanishing"]
abbrev NegativeSelfExtVanishing (G : OpenFamily X 𝓑) : Prop :=
  ∀ (U : Opens X.carrier) (hU : U ∈ 𝓑) (i : ℤ), i < 0 →
    IsZero (AddCommGrpCat.of (Ext⁽i⁾(G.obj U hU, G.obj U hU)))

/-- Basiswise restriction isomorphisms from an ambient derived module to the local objects. -/
@[stacks 0D67 "local identifications of an open-family realization"]
abbrev LocalIso (G : OpenFamily X 𝓑) (K : ModuleDerived X) :=
  ∀ (U : Opens X.carrier) (hU : U ∈ 𝓑),
    (moduleRestrictionToOpenDerived X U).obj K ≅ G.obj U hU

/-- The local identifications of an ambient object respect every prescribed restriction
isomorphism. -/
@[stacks 0D67 "compatibility of an open-family realization"]
def IsRealization (G : OpenFamily X 𝓑) (K : ModuleDerived X) (e : G.LocalIso K) : Prop :=
  ∀ (U V : Opens X.carrier) (hU : U ∈ 𝓑) (hV : V ∈ 𝓑) (hVU : V ≤ U),
    CommSq ((derivedCompIso X hVU).app K).inv (e V hV).hom
      ((derivedBetween X hVU).map (e U hU).hom) (G.ρ U V hU hV hVU).inv

/-- A realization of open-family gluing data by one ambient derived module. -/
@[stacks 0D67 "realization of derived open-family gluing data"]
structure Realization (G : OpenFamily X 𝓑) (K : ModuleDerived X) where
  /-- The basiswise identifications with the local objects. -/
  iso : G.LocalIso K
  /-- The identifications commute with all restriction isomorphisms. -/
  compatible : G.IsRealization K iso

/-- An ambient object realizes the gluing data when compatible local identifications exist. -/
@[stacks 0D67 "existence of an open-family realization"]
abbrev Realizes (G : OpenFamily X 𝓑) (K : ModuleDerived X) : Prop :=
  Nonempty (G.Realization K)

/-- The gluing datum admits some ambient realization. -/
@[stacks 0D67 "existence of an ambient realization"]
abbrev HasRealization (G : OpenFamily X 𝓑) : Prop :=
  ∃ K : ModuleDerived X, G.Realizes K

/-- Source-facing existential form of the bundled realization predicate. -/
@[stacks 0D67 "existential characterization of realizations"]
theorem realizes_iff_exists (G : OpenFamily X 𝓑) (K : ModuleDerived X) :
    G.Realizes K ↔ ∃ e : G.LocalIso K, G.IsRealization K e := sorry

/-- One compatibility square of a raw realization family. -/
@[stacks 0D67 "open-family realization square"]
theorem IsRealization.commSq {G : OpenFamily X 𝓑} {K : ModuleDerived X}
    {e : G.LocalIso K} (h : G.IsRealization K e)
    (U V : Opens X.carrier) (hU : U ∈ 𝓑) (hV : V ∈ 𝓑) (hVU : V ≤ U) :
    CommSq ((derivedCompIso X hVU).app K).inv (e V hV).hom
      ((derivedBetween X hVU).map (e U hU).hom) (G.ρ U V hU hV hVU).inv := sorry

/-- Equational form of one raw realization compatibility square. -/
@[stacks 0D67 "open-family realization equation"]
theorem IsRealization.w {G : OpenFamily X 𝓑} {K : ModuleDerived X}
    {e : G.LocalIso K} (h : G.IsRealization K e)
    (U V : Opens X.carrier) (hU : U ∈ 𝓑) (hV : V ∈ 𝓑) (hVU : V ≤ U) :
    ((derivedCompIso X hVU).app K).inv ≫
        (derivedBetween X hVU).map (e U hU).hom =
      (e V hV).hom ≫ (G.ρ U V hU hV hVU).inv := sorry

/-- The compatibility square carried by a bundled realization. -/
@[stacks 0D67 "bundled open-family realization square"]
theorem Realization.commSq {G : OpenFamily X 𝓑} {K : ModuleDerived X}
    (R : G.Realization K) (U V : Opens X.carrier)
    (hU : U ∈ 𝓑) (hV : V ∈ 𝓑) (hVU : V ≤ U) :
    CommSq ((derivedCompIso X hVU).app K).inv (R.iso V hV).hom
      ((derivedBetween X hVU).map (R.iso U hU).hom) (G.ρ U V hU hV hVU).inv := sorry

/-- An isomorphism of ambient objects is compatible with two realizations when its restrictions
intertwine all their local identifications. -/
@[stacks 0D67 "compatible isomorphism between open-family realizations"]
abbrev IsCompatibleIso {G : OpenFamily X 𝓑} {K L : ModuleDerived X}
    (R : G.Realization K) (S : G.Realization L) (e : K ≅ L) : Prop :=
  ∀ (U : Opens X.carrier) (hU : U ∈ 𝓑),
    CommSq ((moduleRestrictionToOpenDerived X U).map e.hom)
      (R.iso U hU).hom (S.iso U hU).hom (𝟙 (G.obj U hU))

/-- One local square of a compatible isomorphism between realizations. -/
@[stacks 0D67 "local square of a compatible realization isomorphism"]
theorem IsCompatibleIso.commSq {G : OpenFamily X 𝓑} {K L : ModuleDerived X}
    {R : G.Realization K} {S : G.Realization L} {e : K ≅ L}
    (h : IsCompatibleIso R S e) (U : Opens X.carrier) (hU : U ∈ 𝓑) :
    CommSq ((moduleRestrictionToOpenDerived X U).map e.hom)
      (R.iso U hU).hom (S.iso U hU).hom (𝟙 (G.obj U hU)) := sorry

/-- Equational form of compatibility of an isomorphism between realizations. -/
@[stacks 0D67 "equation for a compatible realization isomorphism"]
theorem IsCompatibleIso.w {G : OpenFamily X 𝓑} {K L : ModuleDerived X}
    {R : G.Realization K} {S : G.Realization L} {e : K ≅ L}
    (h : IsCompatibleIso R S e) (U : Opens X.carrier) (hU : U ∈ 𝓑) :
    (moduleRestrictionToOpenDerived X U).map e.hom ≫ (S.iso U hU).hom =
      (R.iso U hU).hom := sorry

end OpenFamily

end AlgebraicGeometry.RingedSpace.ModuleDerived.Gluing

end
