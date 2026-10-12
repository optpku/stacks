/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BaseChange
public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.OfModule
import Mathlib.Tactic.CrossRefAttribute

/-!
# Formal Gluing Across a Ring Map

A formal gluing object consists of a module over the target ring, gluing data
over a principal-open family in the source ring, and an isomorphism between
the two induced target-side gluing objects.

@stack 05EL
-/

@[expose] public section

open CategoryTheory

universe u v w

noncomputable section

namespace LocalizedModule.Away

variable {R S : Type u} [CommRing R] [CommRing S]
variable {ι : Type w}

/-- A formal gluing object for `φ : R →+* S` and a principal-open family
`f : ι → R`.  Its comparison is an isomorphism of complete gluing data, so
pairwise-overlap compatibility is part of that isomorphism rather than a
separate carrier-level equation. -/
@[stacks 05EL "formal principal-open module gluing"]
structure FormalGluing (φ : R →+* S) (f : ι → R) where
  /-- The global module over the target ring. -/
  globalModule : ModuleCat.{max u v} S
  /-- The gluing datum over the source principal-open family. -/
  sourceGluing : Gluing f
  /-- The target-side gluing of the global module agrees with base change of
  the source gluing datum. -/
  comparisonIso :
    Gluing.ofModule (fun i ↦ φ (f i)) globalModule ≅
      sourceGluing.baseChange φ

namespace FormalGluing

variable {φ : R →+* S} {f : ι → R}

/-- A morphism of formal gluing objects consists of maps on the target module
and source gluing datum whose induced target-side square commutes. -/
@[stacks 05EL "formal principal-open gluing morphism"]
structure Hom (X Y : FormalGluing φ f) where
  /-- The map on global target-ring modules. -/
  globalMap : X.globalModule ⟶ Y.globalModule
  /-- The map on source principal-open gluing data. -/
  sourceMap : X.sourceGluing ⟶ Y.sourceGluing
  /-- Compatibility with the comparison isomorphisms after passing both maps
  to the target-side gluing category. -/
  comm :
    CommSq
      (Gluing.ofModuleMap (fun i ↦ φ (f i)) globalMap)
      X.comparisonIso.hom
      Y.comparisonIso.hom
      (Gluing.baseChangeMap φ sourceMap)

namespace Hom

/-- Two morphisms of formal gluing objects are equal when their global and
source-gluing components are equal. -/
@[ext, stacks 05EL "formal gluing morphism extensionality"]
theorem ext {X Y : FormalGluing φ f} {α β : Hom X Y}
    (hglobal : α.globalMap = β.globalMap)
    (hsource : α.sourceMap = β.sourceMap) :
    α = β := sorry

/-- Identity components form a commuting comparison square. -/
@[stacks 05EL "formal gluing identity comparison square"]
theorem id_comm (X : FormalGluing φ f) :
    CommSq
      (Gluing.ofModuleMap (fun i ↦ φ (f i)) (𝟙 X.globalModule))
      X.comparisonIso.hom
      X.comparisonIso.hom
      (Gluing.baseChangeMap φ (𝟙 X.sourceGluing)) := sorry

/-- The identity morphism of a formal gluing object. -/
@[stacks 05EL "formal gluing identity morphism"]
noncomputable def id (X : FormalGluing φ f) : Hom X X where
  globalMap := 𝟙 X.globalModule
  sourceMap := 𝟙 X.sourceGluing
  comm := id_comm X

/-- Composite global and source maps form a commuting comparison square. -/
@[stacks 05EL "formal gluing composition comparison square"]
theorem comp_comm {X Y Z : FormalGluing φ f}
    (α : Hom X Y) (β : Hom Y Z) :
    CommSq
      (Gluing.ofModuleMap (fun i ↦ φ (f i))
        (α.globalMap ≫ β.globalMap))
      X.comparisonIso.hom
      Z.comparisonIso.hom
      (Gluing.baseChangeMap φ (α.sourceMap ≫ β.sourceMap)) := sorry

/-- Composition of morphisms of formal gluing objects. -/
@[stacks 05EL "formal gluing morphism composition"]
noncomputable def comp {X Y Z : FormalGluing φ f}
    (α : Hom X Y) (β : Hom Y Z) : Hom X Z where
  globalMap := α.globalMap ≫ β.globalMap
  sourceMap := α.sourceMap ≫ β.sourceMap
  comm := comp_comm α β

/-- Left identity for morphisms of formal gluing objects. -/
@[stacks 05EL "formal gluing morphism left identity"]
theorem id_comp {X Y : FormalGluing φ f} (α : Hom X Y) :
    comp (id X) α = α := sorry

/-- Right identity for morphisms of formal gluing objects. -/
@[stacks 05EL "formal gluing morphism right identity"]
theorem comp_id {X Y : FormalGluing φ f} (α : Hom X Y) :
    comp α (id Y) = α := sorry

/-- Associativity of composition for morphisms of formal gluing objects. -/
@[stacks 05EL "formal gluing morphism associativity"]
theorem assoc {W X Y Z : FormalGluing φ f}
    (α : Hom W X) (β : Hom X Y) (γ : Hom Y Z) :
    comp (comp α β) γ = comp α (comp β γ) := sorry

end Hom

/-- Formal gluing objects form a category under compatible global and local
maps. -/
@[stacks 05EL "formal principal-open gluing category"]
noncomputable instance instCategory : Category (FormalGluing φ f) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

/-- The global component of the identity formal-gluing morphism is the
identity module morphism. -/
@[stacks 05EL "formal gluing global projection identity"]
theorem globalMap_id (X : FormalGluing φ f) :
    (𝟙 X : X ⟶ X).globalMap = 𝟙 X.globalModule := sorry

/-- The global component of a composite formal-gluing morphism is the
composite of its global components. -/
@[stacks 05EL "formal gluing global projection composition"]
theorem globalMap_comp {X Y Z : FormalGluing φ f}
    (α : X ⟶ Y) (β : Y ⟶ Z) :
    (α ≫ β).globalMap = α.globalMap ≫ β.globalMap := sorry

/-- The global target-ring module underlying a formal gluing object,
functorially in compatible morphisms. -/
@[stacks 05EL "formal gluing global-module functor"]
noncomputable def globalModuleFunctor :
    FormalGluing φ f ⥤ ModuleCat.{max u v} S where
  obj X := X.globalModule
  map α := α.globalMap
  map_id := globalMap_id
  map_comp := globalMap_comp

/-- The source-gluing component of the identity formal-gluing morphism is
the identity gluing morphism. -/
@[stacks 05EL "formal gluing source projection identity"]
theorem sourceMap_id (X : FormalGluing φ f) :
    (𝟙 X : X ⟶ X).sourceMap = 𝟙 X.sourceGluing := sorry

/-- The source-gluing component of a composite is the composite of the
source-gluing components. -/
@[stacks 05EL "formal gluing source projection composition"]
theorem sourceMap_comp {X Y Z : FormalGluing φ f}
    (α : X ⟶ Y) (β : Y ⟶ Z) :
    (α ≫ β).sourceMap = α.sourceMap ≫ β.sourceMap := sorry

/-- The source principal-open gluing datum underlying a formal gluing object,
functorially in compatible morphisms. -/
@[stacks 05EL "formal gluing source-gluing functor"]
noncomputable def sourceGluingFunctor :
    FormalGluing φ f ⥤ Gluing f where
  obj X := X.sourceGluing
  map α := α.sourceMap
  map_id := sourceMap_id
  map_comp := sourceMap_comp

/-- The target-side gluing functor obtained from the global module of a
formal gluing object. -/
@[stacks 05EL "formal gluing global target-side functor"]
noncomputable def globalTargetFunctor :
    FormalGluing φ f ⥤ Gluing (fun i ↦ φ (f i)) :=
  globalModuleFunctor ⋙ Gluing.ofModuleFunctor (fun i ↦ φ (f i))

/-- The target-side gluing functor obtained by base-changing the source
gluing datum. -/
@[stacks 05EL "formal gluing base-changed source functor"]
noncomputable def sourceBaseChangeFunctor :
    FormalGluing φ f ⥤ Gluing (fun i ↦ φ (f i)) :=
  sourceGluingFunctor ⋙ Gluing.baseChangeFunctor φ

/-- The comparison isomorphisms of formal gluing objects are natural in
formal-gluing morphisms. -/
@[stacks 05EL "formal gluing comparison naturality"]
theorem comparison_naturality {X Y : FormalGluing φ f} (α : X ⟶ Y) :
    (globalTargetFunctor.map α) ≫ Y.comparisonIso.hom =
      X.comparisonIso.hom ≫ sourceBaseChangeFunctor.map α := sorry

/-- The objectwise formal-gluing comparisons assemble into a natural
isomorphism from global localization to source-gluing base change. -/
@[stacks 05EL "formal gluing comparison natural isomorphism"]
noncomputable def comparisonNatIso :
    globalTargetFunctor (φ := φ) (f := f) ≅
      sourceBaseChangeFunctor (φ := φ) (f := f) :=
  NatIso.ofComponents (fun X ↦ X.comparisonIso)
    (fun α ↦ comparison_naturality α)

end FormalGluing

end LocalizedModule.Away
