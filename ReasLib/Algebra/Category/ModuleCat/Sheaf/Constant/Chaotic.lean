/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Derived
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Constant
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Restriction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
public import ReasLib.CategoryTheory.Sites.Chaotic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Chaotic constant-ring module presentations

On the chaotic site, a module sheaf over the constant ring sheaf is canonically presented by a
module-valued presheaf.  This leaf records that presentation as an equivalence and its exact
derived-category transport.  The chosen derived-category localizations remain explicit inputs;
the equivalence itself is an ordinary concrete functor, not a choice of derived model.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Sheaf

noncomputable section

universe q q' u v w

namespace ModuleCat.Presheaf.Chaotic

variable {C : Type u} [Category.{v} C]
variable {B : Type w} [Ring B]

namespace Constant

/-- The constant ring presheaf with value `B`. -/
@[stacks 08PF "constant ring presheaf"]
abbrev ringPresheaf : Cᵒᵖ ⥤ RingCat.{w} :=
  (Functor.const Cᵒᵖ).obj (RingCat.of B)

/-- The canonical map from the constant ring presheaf to the corresponding sheaf on the
chaotic site. -/
@[stacks 08PF "constant ring presheaf to chaotic sheaf"]
noncomputable abbrev ringToSheaf :
    ringPresheaf (C := C) (B := B) ⟶
      ((constantSheaf (⊥ : GrothendieckTopology C) RingCat.{w}).obj
        (RingCat.of B)).obj :=
  toSheafify (⊥ : GrothendieckTopology C) (ringPresheaf (C := C) (B := B))

/-- Forget a module sheaf over the constant ring sheaf to a module presheaf over the constant
ring presheaf. -/
@[stacks 08PF "constant module sheaf to constant module presheaf"]
noncomputable abbrev forgetToRing :
    SheafOfModules
        ((constantSheaf (⊥ : GrothendieckTopology C) RingCat.{w}).obj (RingCat.of B)) ⥤
      PresheafOfModules (ringPresheaf (C := C) (B := B)) :=
  SheafOfModules.forget
      ((constantSheaf (⊥ : GrothendieckTopology C) RingCat.{w}).obj (RingCat.of B)) ⋙
    PresheafOfModules.restrictScalars (ringToSheaf (C := C) (B := B))

/-- A section of a module over the constant ring presheaf, regarded as a `B`-module. -/
@[stacks 08PF "constant-ring module object"]
noncomputable def moduleObj
    (M : PresheafOfModules (ringPresheaf (C := C) (B := B))) (X : Cᵒᵖ) :
    _root_.ModuleCat B :=
  @Eq.rec RingCat.{w} ((ringPresheaf (C := C) (B := B)).obj X)
    (fun (R : RingCat.{w}) _ => _root_.ModuleCat R) (M.obj X) (RingCat.of B) rfl

/-- A restriction map over the constant ring presheaf, regarded as a `B`-linear map. -/
@[stacks 08PF "constant-ring module restriction map"]
noncomputable def moduleMap
    (M : PresheafOfModules (ringPresheaf (C := C) (B := B)))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) : moduleObj M X ⟶ moduleObj M Y :=
  _root_.ModuleCat.ofHom (M.map f).hom

/-- Identity law for the restriction maps of the associated `B`-module presheaf. -/
@[stacks 08PF "constant-ring module restriction identity"]
theorem moduleMap_id
    (M : PresheafOfModules (ringPresheaf (C := C) (B := B))) (X : Cᵒᵖ) :
    moduleMap M (𝟙 X) = 𝟙 (moduleObj M X) := sorry

/-- Composition law for the restriction maps of the associated `B`-module presheaf. -/
@[stacks 08PF "constant-ring module restriction composition"]
theorem moduleMap_comp
    (M : PresheafOfModules (ringPresheaf (C := C) (B := B)))
    {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    moduleMap M (f ≫ g) = moduleMap M f ≫ moduleMap M g := sorry

/-- A module over the constant ring presheaf, presented as a `B`-module-valued presheaf. -/
@[stacks 08PF "constant-ring module as module-valued presheaf"]
noncomputable def modulePresheafObj
    (M : PresheafOfModules (ringPresheaf (C := C) (B := B))) :
    _root_.ModuleCat.Presheaf C B where
  obj := moduleObj M
  map := moduleMap M
  map_id := moduleMap_id M
  map_comp := moduleMap_comp M

/-- Naturality of a morphism after presenting constant-ring modules as `B`-module-valued
presheaves. -/
@[stacks 08PF "constant-ring module presheaf map naturality"]
theorem modulePresheafMap_naturality
    {M N : PresheafOfModules (ringPresheaf (C := C) (B := B))} (φ : M ⟶ N)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (modulePresheafObj M).map f ≫ _root_.ModuleCat.ofHom (φ.app Y).hom =
      _root_.ModuleCat.ofHom (φ.app X).hom ≫ (modulePresheafObj N).map f := sorry

/-- A morphism of constant-ring module presheaves, presented objectwise as a morphism of
`B`-module-valued presheaves. -/
@[stacks 08PF "constant-ring module presheaf map"]
noncomputable def modulePresheafMap
    {M N : PresheafOfModules (ringPresheaf (C := C) (B := B))} (φ : M ⟶ N) :
    modulePresheafObj M ⟶ modulePresheafObj N where
  app X := _root_.ModuleCat.ofHom (φ.app X).hom
  naturality := fun {X Y} f => modulePresheafMap_naturality φ f

/-- Identity law for the constant-ring module-presheaf presentation. -/
@[stacks 08PF "constant-ring module presheaf map identity"]
theorem modulePresheafMap_id
    (M : PresheafOfModules (ringPresheaf (C := C) (B := B))) :
    modulePresheafMap (𝟙 M) = 𝟙 (modulePresheafObj M) := sorry

/-- Composition law for the constant-ring module-presheaf presentation. -/
@[stacks 08PF "constant-ring module presheaf map composition"]
theorem modulePresheafMap_comp
    {M N P : PresheafOfModules (ringPresheaf (C := C) (B := B))}
    (φ : M ⟶ N) (ψ : N ⟶ P) :
    modulePresheafMap (φ ≫ ψ) = modulePresheafMap φ ≫ modulePresheafMap ψ := sorry

/-- The concrete functor from modules over the constant ring presheaf to `B`-module-valued
presheaves.  Its object and morphism data are explicit; only the functor laws are deferred. -/
@[stacks 08PF "constant-ring module-presheaf presentation"]
noncomputable def modulePresheaf :
    PresheafOfModules (ringPresheaf (C := C) (B := B)) ⥤ _root_.ModuleCat.Presheaf C B where
  obj := modulePresheafObj
  map := modulePresheafMap
  map_id := modulePresheafMap_id
  map_comp := modulePresheafMap_comp

end Constant

namespace Constant

/-- The constant-module sheaf presentation is an equivalence on the chaotic topology. -/
@[stacks 08PF "chaotic constant-module sheaf equivalence"]
instance sheafFunctor_isEquivalence :
    (Sheaf.ConstantModule.sheafFunctor
      (J := (⊥ : GrothendieckTopology C)) (R := B)).IsEquivalence := sorry

/-- The ordinary functor presenting modules over the constant ring sheaf as `B`-module-valued
presheaves.  Its object and morphism data are the explicit constant-ring construction above;
exactness is exposed separately as reusable instances. -/
@[stacks 08PF "chaotic constant-module ordinary presentation"]
noncomputable abbrev functor :
    SheafOfModules
        ((constantSheaf (⊥ : GrothendieckTopology C) RingCat).obj (RingCat.of B)) ⥤
      _root_.ModuleCat.Presheaf C B :=
  Constant.forgetToRing (C := C) (B := B) ⋙ Constant.modulePresheaf (C := C) (B := B)

/-- The chaotic constant-module presentation preserves finite limits. -/
@[stacks 08PF "chaotic constant-module left exact presentation"]
instance preservesFiniteLimits :
    PreservesFiniteLimits (functor (C := C) (B := B)) := sorry

/-- The chaotic constant-module presentation preserves finite colimits. -/
@[stacks 08PF "chaotic constant-module right exact presentation"]
instance preservesFiniteColimits :
    PreservesFiniteColimits (functor (C := C) (B := B)) := sorry

/-- The chaotic constant-module presentation is additive. -/
@[stacks 08PF "chaotic constant-module additive presentation"]
instance additive :
    (functor (C := C) (B := B)).Additive := sorry

/-- The exact functor underlying the chaotic constant-module presentation. -/
@[stacks 08PF "chaotic constant-module exact presentation"]
noncomputable def exact :
    SheafOfModules
        ((constantSheaf (⊥ : GrothendieckTopology C) RingCat).obj (RingCat.of B)) ⥤ₑ
      _root_.ModuleCat.Presheaf C B :=
  ExactFunctor.of (functor (C := C) (B := B))

section Derived

variable [HasDerivedCategory.{q}
  (SheafOfModules
    ((constantSheaf (⊥ : GrothendieckTopology C) RingCat).obj (RingCat.of B)))]
variable [HasDerivedCategory.{q'} (_root_.ModuleCat.Presheaf C B)]

/-- The induced exact functor between the two derived presentations of `D(underline B)`. -/
@[stacks 08PF "chaotic constant-module derived presentation"]
noncomputable abbrev derived :
      DerivedCategory
        (SheafOfModules
          ((constantSheaf (⊥ : GrothendieckTopology C) RingCat).obj (RingCat.of B))) ⥤
  DerivedCategory (_root_.ModuleCat.Presheaf C B) :=
  (functor (C := C) (B := B)).mapDerivedCategory

/-- The derived chaotic constant-module presentation is an equivalence. -/
@[stacks 08PF "chaotic constant-module derived equivalence"]
theorem derived_isEquivalence :
    (derived (C := C) (B := B)).IsEquivalence := sorry

end Derived

section OfIso

variable {R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{w}}

/-- Present modules over a ring sheaf identified with the constant `B`-sheaf as
`B`-module-valued presheaves.  Restriction of scalars supplies the change-of-rings leg,
and the target presentation is the explicit functor `functor`. -/
@[stacks 09CZ "chaotic module functor transported along a ring-sheaf isomorphism"]
noncomputable abbrev functorOfIso
    (e : R ≅ (constantSheaf (⊥ : GrothendieckTopology C) RingCat).obj (RingCat.of B)) :
    SheafOfModules R ⥤ _root_.ModuleCat.Presheaf C B :=
  SheafOfModules.restrictScalars e.inv ⋙ functor (C := C) (B := B)

/-- The transported chaotic presentation preserves finite limits. -/
@[stacks 09CZ "transported chaotic module presentation preserves finite limits"]
instance preservesFiniteLimitsOfIso
    (e : R ≅ (constantSheaf (⊥ : GrothendieckTopology C) RingCat).obj (RingCat.of B)) :
    PreservesFiniteLimits (functorOfIso e) :=
  sorry

/-- The transported chaotic presentation preserves finite colimits. -/
@[stacks 09CZ "transported chaotic module presentation preserves finite colimits"]
instance preservesFiniteColimitsOfIso
    (e : R ≅ (constantSheaf (⊥ : GrothendieckTopology C) RingCat).obj (RingCat.of B)) :
    PreservesFiniteColimits (functorOfIso e) :=
  sorry

/-- The transported chaotic presentation is additive. -/
@[stacks 09CZ "transported chaotic module presentation is additive"]
instance additiveOfIso
    (e : R ≅ (constantSheaf (⊥ : GrothendieckTopology C) RingCat).obj (RingCat.of B)) :
    (functorOfIso e).Additive :=
  sorry

/-- The exact functor transported along a ring-sheaf isomorphism. -/
@[stacks 09CZ "exact chaotic module presentation transported along a ring-sheaf isomorphism"]
noncomputable def exactOfIso
    (e : R ≅ (constantSheaf (⊥ : GrothendieckTopology C) RingCat).obj (RingCat.of B)) :
    SheafOfModules R ⥤ₑ _root_.ModuleCat.Presheaf C B :=
  ExactFunctor.of (functorOfIso e)

variable [HasDerivedCategory.{q} (SheafOfModules R)]
variable [HasDerivedCategory.{q'} (_root_.ModuleCat.Presheaf C B)]

/-- The derived presentation transported along a ring-sheaf isomorphism. -/
@[stacks 09CZ "derived chaotic module presentation transported along a ring-sheaf isomorphism"]
noncomputable abbrev derivedOfIso
    (e : R ≅ (constantSheaf (⊥ : GrothendieckTopology C) RingCat).obj (RingCat.of B)) :
    DerivedCategory (SheafOfModules R) ⥤
      DerivedCategory (_root_.ModuleCat.Presheaf C B) :=
  (functorOfIso e).mapDerivedCategory

/-- The transported derived presentation is an equivalence. -/
@[stacks 09CZ "derived chaotic module equivalence transported along a ring-sheaf isomorphism"]
theorem derivedOfIso_isEquivalence
    (e : R ≅ (constantSheaf (⊥ : GrothendieckTopology C) RingCat).obj (RingCat.of B)) :
    (derivedOfIso e).IsEquivalence := sorry

end OfIso

section CommRing

variable {S : Type w} [CommRing S]

/-- Forgetting commutativity identifies the constant commutative-ring sheaf with the constant
ring sheaf. -/
@[stacks 09CZ "constant commutative-ring sheaf as a constant ring sheaf"]
def commRingSheafIso :
    CategoryTheory.Sheaf.ringSheafOfComm.{w, u, v}
        ((constantSheaf (⊥ : GrothendieckTopology C) CommRingCat.{w}).obj
          (CommRingCat.of S)) ≅
      (constantSheaf (⊥ : GrothendieckTopology C) RingCat.{w}).obj (RingCat.of S) :=
  (constantCommuteCompose (⊥ : GrothendieckTopology C)
    (forget₂ CommRingCat.{w} RingCat.{w})).app (CommRingCat.of S)

end CommRing

end Constant

end ModuleCat.Presheaf.Chaotic
