/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Action
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Module.Quasicoherent

/-!
# Equivariant quasi-coherent modules for group-scheme actions

This module specializes quasi-coherent modules on a groupoid scheme to the action groupoid
associated to an action of a group scheme.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.Bicategory CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.QCoh.Equivariant

/-- The action groupoid attached to a group-scheme action. -/
abbrev actionGroupoid {S : Scheme.{u}} (G : Grp (Over S)) (X : GroupScheme.Action G) :
    GroupoidScheme S :=
  GroupoidScheme.ofAction G X

/-- The target map of `actionGroupoid G X` is the action morphism. -/
theorem actionGroupoid_t {S : Scheme.{u}} (G : Grp (Over S)) (X : GroupScheme.Action G) :
    (actionGroupoid G X).t.left = (GroupoidScheme.actionTarget G X).left :=
  rfl

/-- The source map of `actionGroupoid G X` is the projection morphism. -/
theorem actionGroupoid_s {S : Scheme.{u}} (G : Grp (Over S)) (X : GroupScheme.Action G) :
    (actionGroupoid G X).s.left = (GroupoidScheme.actionSource G X).left :=
  rfl

/-- The action map `G ×ₛ X ⟶ X` of a bundled action of a group scheme. -/
abbrev action {S : Scheme.{u}} (G : Grp (Over S)) (X : GroupScheme.Action G) :
    (G.X ⊗ X.X).left ⟶ X.X.left :=
  (GroupoidScheme.actionTarget G X).left

/-- The projection `G ×ₛ X ⟶ X` from the product carrying an action. -/
abbrev projection {S : Scheme.{u}} (G : Grp (Over S)) (X : GroupScheme.Action G) :
    (G.X ⊗ X.X).left ⟶ X.X.left :=
  (GroupoidScheme.actionSource G X).left

/-- The cocycle condition for a `G`-linearization, viewed through the action groupoid. -/
abbrev Cocycle {S : Scheme.{u}} (G : Grp (Over S)) (X : GroupScheme.Action G)
    (F : QCoh X.X.left)
    (alpha : (QCoh.pullback (action G X)).obj F ⟶
      (QCoh.pullback (projection G X)).obj F) : Prop :=
  GroupoidScheme.Cocycle (actionGroupoid G X) F alpha

/-- The unit condition for a `G`-linearization, viewed through the action groupoid. -/
abbrev Unit {S : Scheme.{u}} (G : Grp (Over S)) (X : GroupScheme.Action G)
    (F : QCoh X.X.left)
    (alpha : (QCoh.pullback (action G X)).obj F ⟶
      (QCoh.pullback (projection G X)).obj F) : Prop :=
  GroupoidScheme.Unit (actionGroupoid G X) F alpha

/-- The action-groupoid realization of a `G`-equivariant quasi-coherent module. -/
abbrev System {S : Scheme.{u}} (G : Grp (Over S)) (X : GroupScheme.Action G) :=
  GroupoidScheme.System (actionGroupoid G X)

namespace System

/-- The linearization carried by an equivariant system. -/
abbrev alpha {S : Scheme.{u}} {G : Grp (Over S)} {X : GroupScheme.Action G}
    (D : System G X) :
    (QCoh.pullback (action G X)).obj D.obj ⟶
      (QCoh.pullback (projection G X)).obj D.obj :=
  D.action

/-- Construct an equivariant system from its module, linearization, and two laws. -/
abbrev of {S : Scheme.{u}} (G : Grp (Over S)) (X : GroupScheme.Action G)
    (F : QCoh X.X.left)
    (alpha : (QCoh.pullback (action G X)).obj F ⟶
      (QCoh.pullback (projection G X)).obj F)
    (cocycle : Cocycle G X F alpha) (unit : Unit G X F alpha) : System G X :=
  GroupoidScheme.System.of F alpha cocycle unit

/-- The defining laws of an equivariant system, exposed together. -/
theorem spec {S : Scheme.{u}} {G : Grp (Over S)} {X : GroupScheme.Action G}
    (D : System G X) : Cocycle G X D.obj D.alpha ∧ Unit G X D.obj D.alpha :=
  ⟨D.cocycle, D.unit⟩

/-- A morphism of equivariant systems, implemented by the canonical action-groupoid morphism. -/
abbrev Hom {S : Scheme.{u}} {G : Grp (Over S)} {X : GroupScheme.Action G}
    (D E : System G X) :=
  GroupoidScheme.System.Hom D E

namespace Hom

/-- Construct an equivariant morphism from a compatible quasi-coherent-module map. -/
def of {S : Scheme.{u}} {G : Grp (Over S)} {X : GroupScheme.Action G}
    {D E : System G X} (f : D.obj ⟶ E.obj)
    (compatibility : CommSq D.alpha ((QCoh.pullback (action G X)).map f)
      ((QCoh.pullback (projection G X)).map f) E.alpha) : Hom D E :=
  GroupoidScheme.System.Hom.of f compatibility.w.symm

/-- The linearization square of an equivariant morphism as an equality. -/
theorem compatibility_w {S : Scheme.{u}} {G : Grp (Over S)} {X : GroupScheme.Action G}
    {D E : System G X} (f : Hom D E) :
    D.alpha ≫ (QCoh.pullback (projection G X)).map f.hom =
      (QCoh.pullback (action G X)).map f.hom ≫ E.alpha := by
  change D.action ≫ (QCoh.pullback ((actionGroupoid G X).s.left)).map f.hom =
      (QCoh.pullback ((actionGroupoid G X).t.left)).map f.hom ≫ E.action
  exact f.compatibility.symm

/-- Two equivariant morphisms are equal when their underlying maps are equal. -/
theorem ext {S : Scheme.{u}} {G : Grp (Over S)} {X : GroupScheme.Action G}
    {D E : System G X} {f g : Hom D E} (h : f.hom = g.hom) : f = g :=
  GroupoidScheme.System.Hom.ext h

end Hom

end System

end AlgebraicGeometry.Scheme.QCoh.Equivariant

namespace AlgebraicGeometry.Scheme.QCoh

/-- The category of `G`-equivariant quasi-coherent modules on a scheme with `G`-action,
realized as quasi-coherent modules on the associated action groupoid. -/
abbrev Equivariant {S : Scheme.{u}} (G : Grp (Over S)) (X : GroupScheme.Action G) : Cat :=
  GroupoidScheme.QCoh (Scheme.QCoh.Equivariant.actionGroupoid G X)

namespace Equivariant

/-- Construct a `G`-equivariant quasi-coherent module from explicit linearization data. -/
abbrev of {S : Scheme.{u}} (G : Grp (Over S)) (X : GroupScheme.Action G)
    (F : QCoh X.X.left)
    (alpha : (QCoh.pullback (Scheme.QCoh.Equivariant.action G X)).obj F ⟶
      (QCoh.pullback (Scheme.QCoh.Equivariant.projection G X)).obj F)
    (cocycle : Scheme.QCoh.Equivariant.Cocycle G X F alpha)
    (unit : Scheme.QCoh.Equivariant.Unit G X F alpha) : Equivariant G X :=
  GroupoidScheme.QCoh.of F alpha cocycle unit

/-- The underlying quasi-coherent module of an equivariant object. -/
abbrev obj {S : Scheme.{u}} {G : Grp (Over S)} {X : GroupScheme.Action G}
    (D : Equivariant G X) : QCoh X.X.left :=
  GroupoidScheme.QCoh.obj D

/-- The linearization of an equivariant object. -/
abbrev alpha {S : Scheme.{u}} {G : Grp (Over S)} {X : GroupScheme.Action G}
    (D : Equivariant G X) :
    (QCoh.pullback (Scheme.QCoh.Equivariant.action G X)).obj (obj D) ⟶
      (QCoh.pullback (Scheme.QCoh.Equivariant.projection G X)).obj (obj D) :=
  GroupoidScheme.QCoh.action D

/-- The underlying quasi-coherent-module map of an equivariant morphism. -/
abbrev hom {S : Scheme.{u}} {G : Grp (Over S)} {X : GroupScheme.Action G}
    {D E : Equivariant G X} (f : D ⟶ E) : obj D ⟶ obj E :=
  GroupoidScheme.QCoh.hom f

/-- The linearization of an equivariant object satisfies the cocycle law. -/
theorem cocycle {S : Scheme.{u}} {G : Grp (Over S)} {X : GroupScheme.Action G}
    (D : Equivariant G X) :
    Scheme.QCoh.Equivariant.Cocycle G X (obj D) (alpha D) :=
  D.cocycle

/-- The linearization of an equivariant object satisfies the unit law. -/
theorem unit {S : Scheme.{u}} {G : Grp (Over S)} {X : GroupScheme.Action G}
    (D : Equivariant G X) :
    Scheme.QCoh.Equivariant.Unit G X (obj D) (alpha D) :=
  D.unit

/-- The linearization square of an equivariant morphism as an equality. -/
theorem homCompatibility_w {S : Scheme.{u}} {G : Grp (Over S)}
    {X : GroupScheme.Action G} {D E : Equivariant G X} (f : D ⟶ E) :
    alpha D ≫ (QCoh.pullback (Scheme.QCoh.Equivariant.projection G X)).map (hom f) =
      (QCoh.pullback (Scheme.QCoh.Equivariant.action G X)).map (hom f) ≫ alpha E := by
  change GroupoidScheme.QCoh.action D ≫
      (QCoh.pullback ((Scheme.QCoh.Equivariant.actionGroupoid G X).s.left)).map
        (GroupoidScheme.QCoh.hom f) =
    (QCoh.pullback ((Scheme.QCoh.Equivariant.actionGroupoid G X).t.left)).map
        (GroupoidScheme.QCoh.hom f) ≫ GroupoidScheme.QCoh.action E
  exact f.compatibility.symm

/-- An equivariant morphism determines a commutative linearization square. -/
theorem homCompatibility {S : Scheme.{u}} {G : Grp (Over S)}
    {X : GroupScheme.Action G} {D E : Equivariant G X} (f : D ⟶ E) :
    CommSq (alpha D) ((QCoh.pullback (Scheme.QCoh.Equivariant.action G X)).map (hom f))
      ((QCoh.pullback (Scheme.QCoh.Equivariant.projection G X)).map (hom f)) (alpha E) :=
  CommSq.mk (homCompatibility_w f)

/-- Equivariant morphisms are determined by their underlying module maps. -/
theorem homExt {S : Scheme.{u}} {G : Grp (Over S)} {X : GroupScheme.Action G}
    {D E : Equivariant G X} {f g : D ⟶ E} (h : hom f = hom g) : f = g :=
  GroupoidScheme.System.Hom.ext h

end Equivariant

end AlgebraicGeometry.Scheme.QCoh
