/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Torsor.Pseudo

/-!
# Torsors on a site

This leaf adds local nonemptiness and the canonical trivial torsor to the
general pseudo-torsor API.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite

universe w v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A `G`-torsor is a pseudo `G`-torsor whose underlying sheaf is locally
nonempty. -/
@[stacks 03AH]
structure Torsor (G : Sheaf J GrpCat.{w}) extends PseudoTorsor G where
  /-- Every object admits a covering sieve on whose arrows the torsor has sections. -/
  locallyNonempty :
    ∀ U : C,
      ∃ S : Sieve U, S ∈ J U ∧
        ∀ ⦃V : C⦄ (f : V ⟶ U), S f → Nonempty (carrier.1.obj (op V))

namespace Torsor

variable {G : Sheaf J GrpCat.{w}}

/-- Sections of a torsor over an object of the site. -/
abbrev Sections (P : Torsor G) (U : C) : Type w :=
  P.toPseudoTorsor.Sections U

/-- Restriction of torsor sections along a morphism in the site. -/
abbrev res (P : Torsor G) {U V : C} (f : V ⟶ U) : Sections P U → Sections P V :=
  P.toPseudoTorsor.res f

/-- A morphism of torsors is an equivariant morphism of the underlying pseudo torsors. -/
abbrev Hom (P Q : Torsor G) :=
  PseudoTorsor.Hom P.toPseudoTorsor Q.toPseudoTorsor

/-- Restriction maps of a torsor preserve the group action. -/
@[simp]
theorem res_smul (P : Torsor G) {U V : C} (f : V ⟶ U)
    (g : G.1.obj (op U)) (x : Sections P U) :
    P.res f ((P.mulAction U).smul g x) =
      (P.mulAction V).smul (G.1.map f.op g) (P.res f x) :=
  PseudoTorsor.res_smul P.toPseudoTorsor f g x

/-- Translation by a chosen torsor section is bijective. -/
theorem simplyTransitive (P : Torsor G) (U : C) (x : Sections P U) :
    Function.Bijective (fun g : G.1.obj (op U) ↦ (P.mulAction U).smul g x) :=
  PseudoTorsor.simplyTransitive P.toPseudoTorsor U x

/-- The category structure carried explicitly by torsors and equivariant morphisms. -/
@[reducible]
def category : Category (Torsor G) where
  Hom P Q := Hom P Q
  id P := PseudoTorsor.id P.toPseudoTorsor
  comp f g := PseudoTorsor.comp f g
  id_comp := PseudoTorsor.category_id_comp
  comp_id := PseudoTorsor.category_comp_id
  assoc := PseudoTorsor.category_assoc

/-- The bundled category of torsors and equivariant morphisms. -/
def cat (G : Sheaf J GrpCat.{w}) : Cat :=
  ⟨Torsor G, category⟩

/-- An isomorphism of torsors for the explicit torsor category structure. -/
abbrev Iso (P Q : Torsor G) :=
  @CategoryTheory.Iso (Torsor G) category P Q

/-- The setoid identifying torsors that are isomorphic in the explicit torsor category. -/
def isomorphicSetoid (G : Sheaf J GrpCat.{w}) : Setoid (Torsor G) :=
  @CategoryTheory.isIsomorphicSetoid (Torsor G) category

/-- The regular left multiplication action on a sheaf of groups. -/
instance instTrivialMulAction (G : Sheaf J GrpCat.{w}) (U : C) :
    MulAction (G.1.obj (op U)) (((sheafForget J).obj G).1.obj (op U)) :=
  inferInstanceAs (MulAction (G.1.obj (op U)) (G.1.obj (op U)))

/-- Restriction maps of the trivial torsor are equivariant for left multiplication. -/
theorem trivial_act_naturality (G : Sheaf J GrpCat.{w})
    {U V : C} (f : V ⟶ U) (g : G.1.obj (op U))
    (x : ((sheafForget J).obj G).1.obj (op U)) :
    ((sheafForget J).obj G).1.map f.op (g • x) =
      (G.1.map f.op g) • ((sheafForget J).obj G).1.map f.op x := sorry

/-- The regular action of a group on itself is pretransitive. -/
theorem trivial_isPretransitive (G : Sheaf J GrpCat.{w}) (U : C) :
    MulAction.IsPretransitive (G.1.obj (op U)) (((sheafForget J).obj G).1.obj (op U)) := sorry

/-- The regular action of a group on itself is free. -/
theorem trivial_isCancelSMul (G : Sheaf J GrpCat.{w}) (U : C) :
    IsCancelSMul (G.1.obj (op U)) (((sheafForget J).obj G).1.obj (op U)) := sorry

/-- The trivial torsor has locally nonempty fibers on every covering sieve. -/
theorem trivial_locallyNonempty (G : Sheaf J GrpCat.{w}) (U : C) :
    ∃ S : Sieve U, S ∈ J U ∧
      ∀ ⦃V : C⦄ (f : V ⟶ U), S f →
        Nonempty (((sheafForget J).obj G).1.obj (op V)) := sorry

/-- The trivial torsor associated to `G`, with `G` acting on itself by left multiplication. -/
noncomputable def trivial (G : Sheaf J GrpCat.{w}) : Torsor G where
  carrier := (sheafForget J).obj G
  mulAction U := instTrivialMulAction G U
  act_naturality := trivial_act_naturality G
  isPretransitive := trivial_isPretransitive G
  isCancelSMul := trivial_isCancelSMul G
  locallyNonempty := trivial_locallyNonempty G

/-- The canonical section of the trivial torsor over an object of the site. -/
def trivialSection (G : Sheaf J GrpCat.{w}) (U : C) : (trivial G).Sections U :=
  (1 : G.1.obj (op U))

/-- Restricting the canonical section of the trivial torsor gives the canonical section. -/
theorem res_trivialSection (G : Sheaf J GrpCat.{w}) {U V : C} (f : V ⟶ U) :
    (trivial G).res f (trivialSection G U) = trivialSection G V := sorry

/-- A torsor is trivial if it is isomorphic to the canonical trivial torsor. -/
abbrev IsTrivial (P : Torsor G) : Prop :=
  Nonempty (Iso P (trivial G))

end Torsor

end CategoryTheory.Sheaf
