/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.GroupTheory.GroupAction.Transitive
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Pseudo torsors on a site

This leaf gives the site-independent data of a pseudo torsor under a sheaf of
groups, together with equivariant morphisms.  Local nonemptiness is added by
`ReasLib.CategoryTheory.Sites.Torsor.Basic`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite MulAction

universe w v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A pseudo `G`-torsor on a site is a sheaf of sets with a sectionwise
simply transitive action of the sheaf of groups `G`. -/
@[stacks 03AH]
structure PseudoTorsor (G : Sheaf J GrpCat.{w}) where
  /-- The underlying sheaf of sets. -/
  carrier : Sheaf J (Type w)
  /-- The objectwise left action of `G` on the underlying sheaf of sets. -/
  mulAction (U : C) : MulAction (G.1.obj (op U)) (carrier.1.obj (op U))
  /-- Restriction maps are equivariant for the action. -/
  act_naturality {U V : C} (f : V ⟶ U) (g : G.1.obj (op U)) (x : carrier.1.obj (op U)) :
    carrier.1.map f.op ((mulAction U).smul g x) =
      (mulAction V).smul (G.1.map f.op g) (carrier.1.map f.op x)
  /-- Each sectionwise action is pretransitive. -/
  isPretransitive (U : C) :
    @MulAction.IsPretransitive (G.1.obj (op U)) (carrier.1.obj (op U))
      (mulAction U).toSMul
  /-- Each sectionwise action is free. -/
  isCancelSMul (U : C) :
    @IsCancelSMul (G.1.obj (op U)) (carrier.1.obj (op U)) (mulAction U).toSMul

namespace PseudoTorsor

variable {G : Sheaf J GrpCat.{w}}

/-- Sections of a pseudo torsor over an object of the site. -/
abbrev Sections (P : PseudoTorsor G) (U : C) : Type w :=
  P.carrier.1.obj (op U)

/-- Restriction of pseudo-torsor sections along a morphism in the site. -/
abbrev res (P : PseudoTorsor G) {U V : C} (f : V ⟶ U) : Sections P U → Sections P V :=
  P.carrier.1.map f.op

/-- The pseudo-torsor action viewed on an object of the opposite site. -/
@[implicit_reducible]
def opMulAction (P : PseudoTorsor G) (U : Cᵒᵖ) :
    MulAction (G.1.obj U) (P.carrier.1.obj U) :=
  P.mulAction U.unop

/-- The stored pseudo-torsor action evaluated at an object of the opposite site. -/
abbrev instMulActionOp (P : PseudoTorsor G) (U : Cᵒᵖ) :
    MulAction (G.1.obj U) (P.carrier.1.obj U) :=
  opMulAction P U

/-- The opposite-site pseudo-torsor action is pretransitive. -/
theorem opIsPretransitive (P : PseudoTorsor G) (U : Cᵒᵖ) :
    @MulAction.IsPretransitive (G.1.obj U) (P.carrier.1.obj U)
      (opMulAction P U).toSMul :=
  P.isPretransitive U.unop

/-- The opposite-site pseudo-torsor action is free. -/
theorem opIsCancelSMul (P : PseudoTorsor G) (U : Cᵒᵖ) :
    @IsCancelSMul (G.1.obj U) (P.carrier.1.obj U) (opMulAction P U).toSMul :=
  P.isCancelSMul U.unop

/-- Restriction maps of a pseudo torsor preserve the group action. -/
@[simp]
theorem res_smul (P : PseudoTorsor G) {U V : C} (f : V ⟶ U)
    (g : G.1.obj (op U)) (x : Sections P U) :
    P.res f ((P.mulAction U).smul g x) =
      (P.mulAction V).smul (G.1.map f.op g) (P.res f x) := sorry

/-- Translation by a chosen pseudo-torsor section is bijective. -/
theorem simplyTransitive (P : PseudoTorsor G) (U : C) (x : Sections P U) :
    Function.Bijective (fun g : G.1.obj (op U) ↦ (P.mulAction U).smul g x) := sorry

/-- A morphism of pseudo torsors is an equivariant morphism of their underlying sheaves. -/
structure Hom (P Q : PseudoTorsor G) where
  /-- The underlying morphism of sheaves of sets. -/
  hom : P.carrier ⟶ Q.carrier
  /-- The underlying sheaf map is equivariant for the `G`-actions. -/
  comm (U : C) (g : G.1.obj (op U)) (x : Sections P U) :
    hom.1.app (op U) ((P.mulAction U).smul g x) =
      (Q.mulAction U).smul g (hom.1.app (op U) x)

namespace Hom

/-- The value of a pseudo-torsor morphism on sections over `U`. -/
abbrev app {P Q : PseudoTorsor G} (f : Hom P Q) (U : C) :
    Sections P U → Sections Q U :=
  f.hom.1.app (op U)

/-- A pseudo-torsor morphism is equivariant on sections. -/
@[simp]
theorem app_smul {P Q : PseudoTorsor G} (f : Hom P Q) (U : C)
    (g : G.1.obj (op U)) (x : Sections P U) :
    f.app U ((P.mulAction U).smul g x) =
      (Q.mulAction U).smul g (f.app U x) := sorry

end Hom

/-- Two pseudo-torsor morphisms are equal if their underlying sheaf maps agree. -/
theorem Hom.ext_hom {P Q : PseudoTorsor G} {f g : Hom P Q} (h : f.hom = g.hom) : f = g := sorry

/-- Pseudo-torsor morphisms are determined by their values on every section. -/
@[ext]
theorem Hom.ext {P Q : PseudoTorsor G} {f g : Hom P Q}
    (h : ∀ U : C, ∀ x : Sections P U, f.app U x = g.app U x) : f = g := sorry

/-- The identity sheaf morphism is equivariant for the stored pseudo-torsor action. -/
theorem id_comm (P : PseudoTorsor G) (U : C) (g : G.1.obj (op U))
    (x : Sections P U) :
    (𝟙 P.carrier : P.carrier ⟶ P.carrier).1.app (op U) ((P.mulAction U).smul g x) =
      (P.mulAction U).smul g
        ((𝟙 P.carrier : P.carrier ⟶ P.carrier).1.app (op U) x) := sorry

/-- The identity equivariant morphism of a pseudo torsor. -/
def id (P : PseudoTorsor G) : Hom P P where
  hom := 𝟙 P.carrier
  comm := id_comm P

/-- A composite of equivariant sheaf morphisms is equivariant. -/
theorem comp_comm {P Q R : PseudoTorsor G} (f : Hom P Q) (g : Hom Q R)
    (U : C) (a : G.1.obj (op U)) (x : Sections P U) :
    (f.hom ≫ g.hom).1.app (op U) ((P.mulAction U).smul a x) =
      (R.mulAction U).smul a ((f.hom ≫ g.hom).1.app (op U) x) := sorry

/-- Composition of equivariant morphisms of pseudo torsors. -/
def comp {P Q R : PseudoTorsor G} (f : Hom P Q) (g : Hom Q R) : Hom P R where
  hom := f.hom ≫ g.hom
  comm := comp_comm f g

/-- Left composition with the identity equivariant morphism is neutral. -/
theorem category_id_comp {P Q : PseudoTorsor G} (f : Hom P Q) :
    comp (id P) f = f := sorry

/-- Right composition with the identity equivariant morphism is neutral. -/
theorem category_comp_id {P Q : PseudoTorsor G} (f : Hom P Q) :
    comp f (id Q) = f := sorry

/-- Composition of equivariant pseudo-torsor morphisms is associative. -/
theorem category_assoc {P Q R T : PseudoTorsor G}
    (f : Hom P Q) (g : Hom Q R) (h : Hom R T) :
    comp (comp f g) h = comp f (comp g h) := sorry

/-- The explicit category structure on pseudo torsors and equivariant morphisms. -/
@[implicit_reducible]
def category : Category (PseudoTorsor G) where
  Hom P Q := Hom P Q
  id := id
  comp f g := comp f g
  id_comp := category_id_comp
  comp_id := category_comp_id
  assoc := category_assoc

end PseudoTorsor

end CategoryTheory.Sheaf
