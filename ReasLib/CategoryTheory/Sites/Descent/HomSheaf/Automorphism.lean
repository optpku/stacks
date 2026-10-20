/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Conj
public import ReasLib.CategoryTheory.Fibered.InGroupoids.AbelianAutomorphisms
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Pseudofunctor
public import ReasLib.CategoryTheory.Sites.Descent.HomPresheaf.Composition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Automorphism sheaves of fibered groupoids

For a category fibred in groupoids with abelian automorphism groups, this
module constructs its automorphism presheaves and sheaves first in
`CommGrpCat`.  The additive form used by cohomology is then obtained through
mathlib's canonical `CommGrpCat.toAddCommGrp` equivalence, rather than by
declaring a second addition law from categorical composition.
-/

@[expose] public section

universe uC vC uS vS

namespace CategoryTheory

open Opposite
open scoped CategoryTheory.Bicategory

namespace Functor.IsFibered.InGroupoids

variable {C : Type uC} {S : Type uS}
variable [Category.{vC} C] [Category.{vS} S]
variable (p : S ⥤ C) [Functor.IsFibered.InGroupoids p]
variable [Automorphism.IsAbelian p]

/-- The automorphism group of the reindexing of `x` along an object of the
slice category, packaged in `CommGrpCat`. -/
noncomputable def Automorphism.commGrp.sectionValue
    {U : C} (x : p.Fiber U) (T : Over U) : CommGrpCat :=
  Automorphism.commGrp p
    (((Functor.fiberPseudofunctor p).map T.hom.op.toLoc).toFunctor.obj x)

namespace Automorphism

/-- The underlying restriction function between two automorphism-group
sections. The group structure remains owned by `Automorphism.commGrp.sectionValue`. -/
noncomputable def sectionMap
    {U : C} (x : p.Fiber U) {X Y : (Over U)ᵒᵖ} (f : X ⟶ Y) :
    Automorphism.commGrp.sectionValue p x X.unop →
      Automorphism.commGrp.sectionValue p x Y.unop :=
  ((Functor.fiberPseudofunctor p).presheafHom x x).map f

/-- The restriction map of the canonical automorphism presheaf preserves the
multiplicative automorphism-group law. This is the endomorphism specialization
of `Pseudofunctor.presheafHom_map_comp`. -/
theorem sectionMap_mul
    {U : C} (x : p.Fiber U) {X Y : (Over U)ᵒᵖ} (f : X ⟶ Y)
    (α β : Automorphism.commGrp.sectionValue p x X.unop) :
    sectionMap p x f (α * β) =
      sectionMap p x f α * sectionMap p x f β := sorry

/-- The restriction map between two automorphism-group sections. -/
noncomputable def presheafMap
    {U : C} (x : p.Fiber U) {X Y : (Over U)ᵒᵖ} (f : X ⟶ Y) :
    Automorphism.commGrp.sectionValue p x X.unop ⟶
      Automorphism.commGrp.sectionValue p x Y.unop :=
  CommGrpCat.ofHom <|
    MonoidHom.mk'
      (sectionMap p x f)
      (sectionMap_mul p x f)

/-- The automorphism-group restriction map sends the identity slice arrow to
the identity group homomorphism. -/
theorem presheafMap_id
    {U : C} (x : p.Fiber U) (T : (Over U)ᵒᵖ) :
    presheafMap p x (𝟙 T) =
      𝟙 (Automorphism.commGrp.sectionValue p x T.unop) := sorry

/-- The automorphism-group restriction maps respect composition in the slice
category. -/
theorem presheafMap_comp
    {U : C} (x : p.Fiber U) {X Y Z : (Over U)ᵒᵖ}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    presheafMap p x (f ≫ g) = presheafMap p x f ≫ presheafMap p x g := sorry

end Automorphism

/-- The canonical `CommGrpCat`-valued presheaf of automorphisms of a fiber
object. -/
noncomputable def Automorphism.commGrp.presheaf
    {U : C} (x : p.Fiber U) :
    (Over U)ᵒᵖ ⥤ CommGrpCat where
  obj := fun T ↦ Automorphism.commGrp.sectionValue p x T.unop
  map := fun {_ _} f ↦ Automorphism.presheafMap p x f
  map_id := Automorphism.presheafMap_id p x
  map_comp := Automorphism.presheafMap_comp p x

/-- Forgetting the multiplicative group structure on the automorphism-group
presheaf recovers the canonical type-valued Hom-presheaf. -/
theorem Automorphism.commGrp.presheaf.forget
    {U : C} (x : p.Fiber U) :
    Automorphism.commGrp.presheaf p x ⋙ CategoryTheory.forget CommGrpCat =
      (Functor.fiberPseudofunctor p).presheafHom x x := sorry

/-- The commutative-group-valued automorphism presheaf is a sheaf whenever
the fiber pseudofunctor is a prestack; after forgetting, this is the canonical
Hom-sheaf condition. -/
theorem Automorphism.commGrp.presheaf.isSheaf
    (J : GrothendieckTopology C)
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor p) J]
    {U : C} (x : p.Fiber U) :
    Presheaf.IsSheaf (J.over U) (Automorphism.commGrp.presheaf p x) := sorry

/-- The canonical sheaf of commutative multiplicative automorphism groups of
a fiber object. -/
noncomputable def Automorphism.commGrp.sheaf
    (J : GrothendieckTopology C)
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor p) J]
    {U : C} (x : p.Fiber U) :
    Sheaf (J.over U) CommGrpCat :=
  ⟨Automorphism.commGrp.presheaf p x,
    Automorphism.commGrp.presheaf.isSheaf p J x⟩

/-- Forgetting the group structure on the automorphism-group sheaf recovers
the canonical Hom-sheaf of the fiber pseudofunctor. -/
theorem Automorphism.commGrp.sheaf.forget
    (J : GrothendieckTopology C)
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor p) J]
    {U : C} (x : p.Fiber U) :
    (Automorphism.commGrp.sheaf p J x).1 ⋙ CategoryTheory.forget CommGrpCat =
      ((Functor.fiberPseudofunctor p).sheafHom J x x).1 := sorry

/-- The additive commutative-group-valued automorphism presheaf obtained from
the canonical multiplicative one through `CommGrpCat.toAddCommGrp`. -/
noncomputable def Automorphism.addComm.presheaf
    {U : C} (x : p.Fiber U) :
    (Over U)ᵒᵖ ⥤ AddCommGrpCat :=
  Automorphism.commGrp.presheaf p x ⋙ CommGrpCat.toAddCommGrp

/-- The additive automorphism presheaf is a sheaf whenever the fiber
pseudofunctor is a prestack. -/
theorem Automorphism.addComm.presheaf.isSheaf
    (J : GrothendieckTopology C)
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor p) J]
    {U : C} (x : p.Fiber U) :
    Presheaf.IsSheaf (J.over U) (Automorphism.addComm.presheaf p x) := sorry

/-- The additive commutative-group-valued automorphism sheaf used by sheaf
cohomology. -/
@[stacks 0CJY "additive automorphism sheaf of an abelian fibred groupoid"]
noncomputable def Automorphism.addComm.sheaf
    (J : GrothendieckTopology C)
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor p) J]
    {U : C} (x : p.Fiber U) :
    Sheaf (J.over U) AddCommGrpCat :=
  ⟨Automorphism.addComm.presheaf p x,
    Automorphism.addComm.presheaf.isSheaf p J x⟩

/-- Forgetting the additive structure on the additive automorphism sheaf
agrees with forgetting the multiplicative structure on its primary
`CommGrpCat`-valued form. -/
theorem Automorphism.addComm.sheaf.forget
    (J : GrothendieckTopology C)
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor p) J]
    {U : C} (x : p.Fiber U) :
    (Automorphism.addComm.sheaf p J x).1 ⋙ CategoryTheory.forget AddCommGrpCat =
      (Automorphism.commGrp.sheaf p J x).1 ⋙ CategoryTheory.forget CommGrpCat := sorry

/-- Forgetting the additive structure on the automorphism sheaf recovers the
canonical type-valued Hom-sheaf directly. -/
theorem Automorphism.addComm.sheaf.forget_eq_sheafHom
    (J : GrothendieckTopology C)
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor p) J]
    {U : C} (x : p.Fiber U) :
    (Automorphism.addComm.sheaf p J x).1 ⋙ CategoryTheory.forget AddCommGrpCat =
      ((Functor.fiberPseudofunctor p).sheafHom J x x).1 := sorry

namespace Automorphism

/-- The underlying conjugation function on one automorphism-group section. -/
noncomputable def conjAppFun
    {U : C} {x y : p.Fiber U} (e : x ≅ y) (T : (Over U)ᵒᵖ) :
    Automorphism.commGrp.sectionValue p x T.unop →
      Automorphism.commGrp.sectionValue p y T.unop :=
  fun α ↦
    (((Functor.fiberPseudofunctor p).map T.unop.hom.op.toLoc).toFunctor.mapIso e).conj α

/-- Conjugation by a fiber isomorphism preserves the multiplicative law on
automorphism-group sections. -/
theorem conjAppFun_mul
    {U : C} {x y : p.Fiber U} (e : x ≅ y) (T : (Over U)ᵒᵖ)
    (α β : Automorphism.commGrp.sectionValue p x T.unop) :
    conjAppFun p e T (α * β) =
      conjAppFun p e T α * conjAppFun p e T β := sorry

/-- Conjugation by a fiber isomorphism on one section of the canonical
commutative automorphism-group presheaf. -/
noncomputable def conjApp
    {U : C} {x y : p.Fiber U} (e : x ≅ y) (T : (Over U)ᵒᵖ) :
    (Automorphism.commGrp.presheaf p x).obj T ⟶
      (Automorphism.commGrp.presheaf p y).obj T :=
  CommGrpCat.ofHom <|
    MonoidHom.mk'
      (conjAppFun p e T)
      (conjAppFun_mul p e T)

/-- The sectionwise conjugation maps are inverse to those induced by the
inverse fiber isomorphism. -/
theorem conjApp_hom_inv_id
    {U : C} {x y : p.Fiber U} (e : x ≅ y) (T : (Over U)ᵒᵖ) :
    conjApp p e T ≫ conjApp p e.symm T =
      𝟙 ((Automorphism.commGrp.presheaf p x).obj T) := sorry

/-- The sectionwise conjugation maps induced by inverse fiber isomorphisms
compose in the reverse order to the identity. -/
theorem conjApp_inv_hom_id
    {U : C} {x y : p.Fiber U} (e : x ≅ y) (T : (Over U)ᵒᵖ) :
    conjApp p e.symm T ≫ conjApp p e T =
      𝟙 ((Automorphism.commGrp.presheaf p y).obj T) := sorry

/-- The sectionwise automorphism-group conjugation isomorphism. -/
noncomputable def conjAppIso
    {U : C} {x y : p.Fiber U} (e : x ≅ y) (T : (Over U)ᵒᵖ) :
    (Automorphism.commGrp.presheaf p x).obj T ≅
      (Automorphism.commGrp.presheaf p y).obj T where
  hom := conjApp p e T
  inv := conjApp p e.symm T
  hom_inv_id := conjApp_hom_inv_id p e T
  inv_hom_id := conjApp_inv_hom_id p e T

/-- Sectionwise automorphism-group conjugation commutes with restriction in
the localized site. -/
theorem conjApp_naturality
    {U : C} {x y : p.Fiber U} (e : x ≅ y)
    {X Y : (Over U)ᵒᵖ} (f : X ⟶ Y) :
    (Automorphism.commGrp.presheaf p x).map f ≫
        conjApp p e Y =
      conjApp p e X ≫
        (Automorphism.commGrp.presheaf p y).map f := sorry

end Automorphism

/-- Conjugation by a fiber isomorphism, promoted to an isomorphism of the
canonical commutative automorphism-group presheaves. -/
noncomputable def Automorphism.commGrp.presheaf.conj
    {U : C} {x y : p.Fiber U} (e : x ≅ y) :
    Automorphism.commGrp.presheaf p x ≅ Automorphism.commGrp.presheaf p y :=
  NatIso.ofComponents
    (fun T ↦ Automorphism.conjAppIso p e T)
    (fun {_ _} f ↦ Automorphism.conjApp_naturality p e f)

/-- Conjugation by a fiber isomorphism, promoted from the automorphism
presheaf to the canonical sheaf of commutative groups. -/
noncomputable def Automorphism.commGrp.sheaf.conj
    (J : GrothendieckTopology C)
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor p) J]
    {U : C} {x y : p.Fiber U} (e : x ≅ y) :
    Automorphism.commGrp.sheaf p J x ≅ Automorphism.commGrp.sheaf p J y :=
  (fullyFaithfulSheafToPresheaf (J.over U) CommGrpCat).preimageIso
    (Automorphism.commGrp.presheaf.conj p e)

/-- Conjugation by a fiber isomorphism of the additive automorphism
presheaves used by sheaf cohomology. This is the image of the primary
`CommGrpCat`-valued construction under `CommGrpCat.toAddCommGrp`. -/
noncomputable def Automorphism.addComm.presheaf.conj
    {U : C} {x y : p.Fiber U} (e : x ≅ y) :
    Automorphism.addComm.presheaf p x ≅ Automorphism.addComm.presheaf p y :=
  Functor.isoWhiskerRight (Automorphism.commGrp.presheaf.conj p e)
    CommGrpCat.toAddCommGrp

/-- Conjugation by a fiber isomorphism of the additive automorphism sheaves
used by sheaf cohomology. -/
@[stacks 0CJY "conjugation of additive automorphism sheaves"]
noncomputable def Automorphism.addComm.sheaf.conj
    (J : GrothendieckTopology C)
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor p) J]
    {U : C} {x y : p.Fiber U} (e : x ≅ y) :
    Automorphism.addComm.sheaf p J x ≅ Automorphism.addComm.sheaf p J y :=
  (fullyFaithfulSheafToPresheaf (J.over U) AddCommGrpCat).preimageIso
    (Automorphism.addComm.presheaf.conj p e)

/-- The additive automorphism-sheaf conjugation attached to an arbitrary
morphism in a fiber groupoid. -/
@[stacks 0CJY "automorphism-sheaf conjugation along a fibre morphism"]
noncomputable def Automorphism.addComm.sheaf.conjOfHom
    (J : GrothendieckTopology C)
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor p) J]
    {U : C} {x y : p.Fiber U} (f : x ⟶ y) :
    Automorphism.addComm.sheaf p J x ≅ Automorphism.addComm.sheaf p J y :=
  Automorphism.addComm.sheaf.conj p J (asIso f)

/-- Additive automorphism-sheaf conjugation is functorial under composition
of fiber isomorphisms. -/
theorem Automorphism.addComm.sheaf.conj_trans
    (J : GrothendieckTopology C)
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor p) J]
    {U : C} {x y z : p.Fiber U} (e₁ : x ≅ y) (e₂ : y ≅ z) :
    Automorphism.addComm.sheaf.conj p J e₁ ≪≫ Automorphism.addComm.sheaf.conj p J e₂ =
      Automorphism.addComm.sheaf.conj p J (e₁ ≪≫ e₂) := sorry

/-- Inner conjugation acts trivially on the additive automorphism sheaf of a
fiber object with abelian automorphism group. -/
theorem Automorphism.addComm.sheaf.conjOfHom_end
    (J : GrothendieckTopology C)
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor p) J]
    {U : C} {x : p.Fiber U} (f : x ⟶ x) :
    Automorphism.addComm.sheaf.conjOfHom p J f = Iso.refl _ := sorry

/-- Parallel morphisms in a fiber groupoid induce the same additive
automorphism-sheaf conjugation isomorphism. -/
theorem Automorphism.addComm.sheaf.conjOfHom_eq_of_parallel
    (J : GrothendieckTopology C)
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor p) J]
    {U : C} {x y : p.Fiber U} (f g : x ⟶ y) :
    Automorphism.addComm.sheaf.conjOfHom p J f =
      Automorphism.addComm.sheaf.conjOfHom p J g := sorry

end Functor.IsFibered.InGroupoids

end CategoryTheory
