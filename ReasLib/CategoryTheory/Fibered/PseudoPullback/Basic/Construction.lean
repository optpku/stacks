/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Fiber
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Construction of pseudo-pullbacks of categories over a base

This leaf owns the private carrier and category structure of the explicit pseudo-pullback of two
based functors, together with its public constructor and structural accessors. Computation rules
and naturality statements are deliberately kept in the sibling `Computations` and `Naturality`
leaves, so clients can choose the lightest interface that supplies their proof API.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open CategoryTheory
open CategoryTheory.Limits
open BasedFunctor
open BasedNatIso
open Functor.IsHomLift
open Functor.Fiber
open CategoricalPullback
open scoped CategoricalPullback
open scoped Bicategory BasedFunctor

universe u v w vB uX vX uY vY uS vS

namespace CategoryTheory

open Bicategory

namespace BasedCategory

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}
variable {S : BasedCategory.{vS, uS} C}
variable (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)

namespace PseudoPullback

/-- Internal object carrier for the explicit pseudo-pullback construction.

The public owner is the bundled based category `BasedCategory.PseudoPullback F G`; its object
data are constructed and inspected through `PseudoPullback.mk`, `baseObj`, `fiberObj`, `fstObj`,
and `sndObj`. Keeping this carrier private prevents implementation fields from becoming a second
public representation of the same object. -/
private structure Obj where
  /-- The common base object. -/
  base : C
  /-- The fibrewise categorical-pullback object over the common base. -/
  fiber : CategoricalPullback (F.fiberFunctor base) (G.fiberFunctor base)

namespace Obj

/-- Internal comparison morphism carried by the pseudo-pullback object representation. -/
private abbrev comparison : (P : Obj F G) → (F.obj P.fiber.fst.1 ⟶ G.obj P.fiber.snd.1)
  | ⟨_, ⟨_, _, i⟩⟩ => i.hom.1

/-- The internal comparison morphism lies over the identity of its common base object. -/
private instance comparison_isHomLift (P : Obj F G) :
    S.p.IsHomLift (𝟙 P.base) P.comparison := sorry
-- Proof strategy: destruct P and extract verticality from its fiber-isomorphism component.

end Obj

/-- Internal morphism carrier for the explicit pseudo-pullback construction.

The public morphism interface is `P ⟶ Q`, together with `PseudoPullback.homMk`, `baseMap`,
`fstMap`, `sndMap`, `comm`, and `hom_ext`. Keeping the carrier private prevents its proof-bearing
fields from becoming a parallel public hom API. -/
private structure HomData (P Q : Obj F G) where
  /-- The common base morphism. -/
  base : P.base ⟶ Q.base
  /-- The morphism on the first component. -/
  fst : P.fiber.fst.1 ⟶ Q.fiber.fst.1
  /-- The first component lies over the common base morphism. -/
  fst_isHomLift : X.p.IsHomLift base fst
  /-- The morphism on the second component. -/
  snd : P.fiber.snd.1 ⟶ Q.fiber.snd.1
  /-- The second component lies over the common base morphism. -/
  snd_isHomLift : Y.p.IsHomLift base snd
  /-- The comparison square commutes. -/
  comm : CommSq (F.toFunctor.map fst) P.comparison Q.comparison (G.toFunctor.map snd)

attribute [instance] HomData.fst_isHomLift HomData.snd_isHomLift

namespace HomData

/-- Implementation pseudo-pullback morphisms are determined by their two component morphisms. -/
@[ext]
private theorem ext {P Q : Obj F G} (φ ψ : HomData F G P Q)
    (hfst : φ.fst = ψ.fst) (hsnd : φ.snd = ψ.snd) : φ = ψ := sorry
-- Proof strategy: recover the base-map equality from hfst and the IsHomLift factorization,
-- then apply structure extensionality.

end HomData

namespace Implementation

/-- The comparison square for the identity implementation pseudo-pullback morphism. -/
private theorem id_comm (P : Obj F G) :
    CommSq (F.toFunctor.map (𝟙 P.fiber.fst.1)) P.comparison P.comparison
      (G.toFunctor.map (𝟙 P.fiber.snd.1)) := sorry
-- Proof strategy: unfold Obj.comparison and simplify both functorial identity maps.

/-- The first component of the identity implementation morphism lies over the identity base map. -/
private theorem id_fst_isHomLift (P : Obj F G) :
    X.p.IsHomLift (𝟙 P.base) (𝟙 P.fiber.fst.1) := sorry
-- Proof strategy: apply IsHomLift.id to the stored first projection equality.

/-- The second component of the identity implementation morphism lies over the identity base map. -/
private theorem id_snd_isHomLift (P : Obj F G) :
    Y.p.IsHomLift (𝟙 P.base) (𝟙 P.fiber.snd.1) := sorry
-- Proof strategy: apply IsHomLift.id to the stored second projection equality.

/-- Identity implementation pseudo-pullback morphism. -/
private def id (P : Obj F G) : HomData F G P P where
  base := 𝟙 P.base
  fst := 𝟙 P.fiber.fst.1
  fst_isHomLift := id_fst_isHomLift F G P
  snd := 𝟙 P.fiber.snd.1
  snd_isHomLift := id_snd_isHomLift F G P
  comm := id_comm F G P

/-- The comparison square remains commutative under composition. -/
private theorem comp_comm {P Q R : Obj F G}
    (φ : HomData F G P Q) (ψ : HomData F G Q R) :
    CommSq (F.toFunctor.map (φ.fst ≫ ψ.fst)) P.comparison R.comparison
      (G.toFunctor.map (φ.snd ≫ ψ.snd)) := sorry
-- Proof strategy: horizontally compose φ.comm and ψ.comm, then rewrite by functoriality.

/-- First components of composable implementation morphisms lift the composite base map. -/
private theorem comp_fst_isHomLift {P Q R : Obj F G}
    (φ : HomData F G P Q) (ψ : HomData F G Q R) :
    X.p.IsHomLift (φ.base ≫ ψ.base) (φ.fst ≫ ψ.fst) := sorry
-- Proof strategy: use closure of IsHomLift under composition.

/-- Second components of composable implementation morphisms lift the composite base map. -/
private theorem comp_snd_isHomLift {P Q R : Obj F G}
    (φ : HomData F G P Q) (ψ : HomData F G Q R) :
    Y.p.IsHomLift (φ.base ≫ ψ.base) (φ.snd ≫ ψ.snd) := sorry
-- Proof strategy: use closure of IsHomLift under composition.

/-- Composition of implementation pseudo-pullback morphisms. -/
private def comp {P Q R : Obj F G}
    (φ : HomData F G P Q) (ψ : HomData F G Q R) : HomData F G P R where
  base := φ.base ≫ ψ.base
  fst := φ.fst ≫ ψ.fst
  fst_isHomLift := comp_fst_isHomLift F G φ ψ
  snd := φ.snd ≫ ψ.snd
  snd_isHomLift := comp_snd_isHomLift F G φ ψ
  comm := comp_comm F G φ ψ

/-- Left identity for implementation pseudo-pullback morphism composition. -/
private theorem id_comp {P Q : Obj F G} (φ : HomData F G P Q) :
    comp F G (id F G P) φ = φ := sorry
-- Proof strategy: apply HomData.ext and simplify the two component maps.

/-- Right identity for implementation pseudo-pullback morphism composition. -/
private theorem comp_id {P Q : Obj F G} (φ : HomData F G P Q) :
    comp F G φ (id F G Q) = φ := sorry
-- Proof strategy: apply HomData.ext and simplify the two component maps.

/-- Associativity for implementation pseudo-pullback morphism composition. -/
private theorem assoc {P Q R T : Obj F G}
    (φ : HomData F G P Q) (ψ : HomData F G Q R) (χ : HomData F G R T) :
    comp F G (comp F G φ ψ) χ = comp F G φ (comp F G ψ χ) := sorry
-- Proof strategy: apply HomData.ext and use associativity in X.obj and Y.obj.

/-- The implementation carrier and morphism data form a category. -/
private instance category : Category (Obj F G) where
  Hom P Q := HomData F G P Q
  id := id F G
  comp := comp F G
  id_comp := id_comp F G
  comp_id := comp_id F G
  assoc := assoc F G

/-- The implementation base projection preserves identity morphisms. -/
private theorem baseFunctor_map_id (P : Obj F G) :
    ((𝟙 P : P ⟶ P) : HomData F G P P).base = 𝟙 P.base := sorry
-- Proof strategy: unfold the implementation identity morphism.

/-- The implementation base projection preserves composition. -/
private theorem baseFunctor_map_comp {P Q R : Obj F G} (φ : P ⟶ Q) (ψ : Q ⟶ R) :
    ((φ ≫ ψ : P ⟶ R) : HomData F G P R).base =
      (φ : HomData F G P Q).base ≫ (ψ : HomData F G Q R).base := sorry
-- Proof strategy: unfold implementation composition.

/-- Implementation projection from the pseudo-pullback carrier to the base. -/
private def baseFunctor : Obj F G ⥤ C where
  obj P := P.base
  map φ := φ.base
  map_id := baseFunctor_map_id F G
  map_comp := baseFunctor_map_comp F G

end Implementation

/-- The canonical pseudo-pullback of based functors `F : X ⥤ᵇ S` and `G : Y ⥤ᵇ S`.

Its private carrier assembles the categorical pullbacks of the induced functors on every fibre,
while a morphism consists of a common base arrow and compatible component arrows. The bundled
based category is the sole public owner; downstream constructions use its `mk`/`homMk`
constructors and the public projection API below.

The object universe is `max u uX uY vS`, since an object stores a base object, two total-category
objects, and an isomorphism in `S`. The morphism universe is `max v vX vY`; the commutativity
condition in `S` is proof-valued and therefore does not enlarge it. -/
@[stacks 0040 "explicit pseudo-pullback of based categories"]
def _root_.CategoryTheory.BasedCategory.PseudoPullback
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) :
    BasedCategory.{max v vX vY, max u uX uY vS} C where
  obj := Obj F G
  category := Implementation.category F G
  p := Implementation.baseFunctor F G

/-- Construct an object from a base object and a fibrewise categorical-pullback object. -/
def mk (U : C) (P : CategoricalPullback (F.fiberFunctor U) (G.fiberFunctor U)) :
    (PseudoPullback F G).obj :=
  ⟨U, P⟩

/-- The common base object of a pseudo-pullback object. -/
abbrev baseObj {F : X ⥤ᵇ S} {G : Y ⥤ᵇ S}
    (P : (PseudoPullback F G).obj) : C :=
  (P : Obj F G).base

/-- The fibrewise categorical-pullback object stored by a pseudo-pullback object. -/
abbrev fiberObj {F : X ⥤ᵇ S} {G : Y ⥤ᵇ S}
    (P : (PseudoPullback F G).obj) :
  CategoricalPullback (F.fiberFunctor (baseObj P))
      (G.fiberFunctor (baseObj P)) :=
  (P : Obj F G).fiber

/-- The first component of a pseudo-pullback object. -/
abbrev fstObj {F : X ⥤ᵇ S} {G : Y ⥤ᵇ S}
    (P : (PseudoPullback F G).obj) : X.obj :=
  (fiberObj P).fst.1

/-- The second component of a pseudo-pullback object. -/
abbrev sndObj {F : X ⥤ᵇ S} {G : Y ⥤ᵇ S}
    (P : (PseudoPullback F G).obj) : Y.obj :=
  (fiberObj P).snd.1

/-- The canonical base isomorphism carried by the first fibre component of a
pseudo-pullback object. It names the dependent transport otherwise exposed as the raw equality
field `(fiberObj P).fst.2`. -/
def fstBaseIso {F : X ⥤ᵇ S} {G : Y ⥤ᵇ S}
    (P : (PseudoPullback F G).obj) :
    X.p.obj (fstObj P) ≅ baseObj P :=
  eqToIso (fiberObj P).fst.2

/-- The canonical base isomorphism carried by the second fibre component of a
pseudo-pullback object. It names the dependent transport otherwise exposed as the raw equality
field `(fiberObj P).snd.2`. -/
def sndBaseIso {F : X ⥤ᵇ S} {G : Y ⥤ᵇ S}
    (P : (PseudoPullback F G).obj) :
    Y.p.obj (sndObj P) ≅ baseObj P :=
  eqToIso (fiberObj P).snd.2

/-- The objectwise comparison isomorphism in the total category of `S`. This is the image of
the isomorphism stored in the fibrewise categorical-pullback object under the canonical fibre
inclusion. -/
def comparisonIsoApp {F : X ⥤ᵇ S} {G : Y ⥤ᵇ S}
    (P : (PseudoPullback F G).obj) :
    F.obj (fstObj P) ≅ G.obj (sndObj P) :=
  (fiberInclusion : S.p.Fiber (baseObj P) ⥤ S.obj).mapIso
    (fiberObj P).iso

/-- The comparison morphism in `S` carried by a pseudo-pullback object. -/
abbrev comparison {F : X ⥤ᵇ S} {G : Y ⥤ᵇ S}
    (P : (PseudoPullback F G).obj) :
    F.obj (fstObj P) ⟶ G.obj (sndObj P) :=
  (P : Obj F G).comparison

/-- Construct a pseudo-pullback morphism from a common base map, two component maps, explicit
lift certificates, and the compatible comparison square. This is the ordinary-argument boundary
for the typeclass-driven `PseudoPullback.homMk`. -/
@[stacks 0040 "explicit pseudo-pullback morphism constructor"]
def Hom.mk {F : X ⥤ᵇ S} {G : Y ⥤ᵇ S}
    {P Q : (PseudoPullback F G).obj}
    (base : baseObj P ⟶ baseObj Q)
    (fst : fstObj P ⟶ fstObj Q)
    (fst_isHomLift : X.p.IsHomLift base fst)
    (snd : sndObj P ⟶ sndObj Q)
    (snd_isHomLift : Y.p.IsHomLift base snd)
    (comm : CommSq (F.toFunctor.map fst) (comparison P) (comparison Q)
      (G.toFunctor.map snd)) :
    P ⟶ Q :=
  { base := base
    fst := fst
    fst_isHomLift := fst_isHomLift
    snd := snd
    snd_isHomLift := snd_isHomLift
    comm := comm }

/-- Construct a pseudo-pullback morphism from a common base map and compatible component maps.
The lifting certificates are inferred because `Functor.IsHomLift` is a class. Use
`Hom.mk` at an explicit-proof boundary. -/
@[stacks 0040 "pseudo-pullback morphism constructor"]
def homMk {F : X ⥤ᵇ S} {G : Y ⥤ᵇ S} {P Q : (PseudoPullback F G).obj}
    (base : baseObj P ⟶ baseObj Q)
    (fst : fstObj P ⟶ fstObj Q) [fst_isHomLift : X.p.IsHomLift base fst]
    (snd : sndObj P ⟶ sndObj Q) [snd_isHomLift : Y.p.IsHomLift base snd]
    (comm : CommSq (F.toFunctor.map fst) (comparison P) (comparison Q)
      (G.toFunctor.map snd)) :
    P ⟶ Q :=
  Hom.mk base fst fst_isHomLift snd snd_isHomLift comm

/-- The common base map underlying a pseudo-pullback morphism. -/
abbrev baseMap {F : X ⥤ᵇ S} {G : Y ⥤ᵇ S}
    {P Q : (PseudoPullback F G).obj} (φ : P ⟶ Q) :
    baseObj P ⟶ baseObj Q :=
  (φ : HomData F G P Q).base

/-- The first component of a pseudo-pullback morphism. -/
abbrev fstMap {F : X ⥤ᵇ S} {G : Y ⥤ᵇ S}
    {P Q : (PseudoPullback F G).obj} (φ : P ⟶ Q) :
    fstObj P ⟶ fstObj Q :=
  (φ : HomData F G P Q).fst

/-- The second component of a pseudo-pullback morphism. -/
abbrev sndMap {F : X ⥤ᵇ S} {G : Y ⥤ᵇ S}
    {P Q : (PseudoPullback F G).obj} (φ : P ⟶ Q) :
    sndObj P ⟶ sndObj Q :=
  (φ : HomData F G P Q).snd

end PseudoPullback
end BasedCategory
end CategoryTheory
