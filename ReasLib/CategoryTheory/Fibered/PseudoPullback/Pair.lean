/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Projections
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pairing based functors into the relative product

Two based functors `F : A ⥤ᵇ X` and `G : A ⥤ᵇ Y` determine a canonical based functor from
`A` to the pseudo-pullback of `X.toBase` and `Y.toBase`. This is the relative-product analogue
of `Functor.prod'`: it retains the common base object and records the canonical comparison
between the two equal images in the base.
-/

@[expose] public section

universe u v uA vA uX vX uY vY

namespace CategoryTheory
namespace BasedCategory.PseudoPullback

open Functor.Fiber
open scoped BasedFunctor

variable {C : Type u} [Category.{v} C]
variable {A : BasedCategory.{vA, uA} C}
variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}

section PairImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

variable (F : A ⥤ᵇ X) (G : A ⥤ᵇ Y)

/-- The canonical base isomorphism between the images of an object under two based functors. -/
private def pairBaseIso (a : A.obj) : X.p.obj (F.obj a) ≅ Y.p.obj (G.obj a) :=
  eqToIso ((F.w_obj a).trans (G.w_obj a).symm)

/-- The forward map of the canonical base isomorphism is vertical over the identity of the
common base object. -/
private theorem pairBaseIso_hom_isHomLift (a : A.obj) :
    (𝟭 C).IsHomLift (𝟙 (A.p.obj a)) (pairBaseIso F G a).hom := sorry

/-- The comparison in the identity fiber induced by the canonical equality of base images. -/
private def pairFiberIso (a : A.obj) :
    ((BasedCategory.toBase X).fiberFunctor (A.p.obj a)).obj
        ⟨F.obj a, F.w_obj a⟩ ≅
      ((BasedCategory.toBase Y).fiberFunctor (A.p.obj a)).obj
        ⟨G.obj a, G.w_obj a⟩ :=
  Functor.Fiber.isoMk (pairBaseIso F G a)
    (hhom := pairBaseIso_hom_isHomLift F G a)

/-- The objectwise pairing of `F.obj a` and `G.obj a` in the relative product of `X` and `Y`. -/
private def pairObj (a : A.obj) :
    (PseudoPullback (BasedCategory.toBase X) (BasedCategory.toBase Y)).obj :=
  mk (BasedCategory.toBase X) (BasedCategory.toBase Y) (A.p.obj a)
    { fst := ⟨F.obj a, F.w_obj a⟩
      snd := ⟨G.obj a, G.w_obj a⟩
      iso := pairFiberIso F G a }

/-- The two component maps of a paired morphism respect the canonical base comparisons. -/
private theorem pairMap_comm {a b : A.obj} (f : a ⟶ b) :
    CommSq
      ((BasedCategory.toBase X).map (F.map f))
      (comparison (pairObj F G a))
      (comparison (pairObj F G b))
      ((BasedCategory.toBase Y).map (G.map f)) := sorry

/-- The morphismwise pairing of `F.map f` and `G.map f` over the common base map. -/
private def pairMap {a b : A.obj} (f : a ⟶ b) : pairObj F G a ⟶ pairObj F G b :=
  PseudoPullback.Hom.mk (A.p.map f)
    (F.map f) (BasedFunctor.preserves_isHomLift F (A.p.map f) f)
    (G.map f) (BasedFunctor.preserves_isHomLift G (A.p.map f) f)
    (pairMap_comm F G f)

/-- Pairing preserves identity morphisms. -/
private theorem pairMap_id (a : A.obj) : pairMap F G (𝟙 a) = 𝟙 (pairObj F G a) := sorry

/-- Pairing preserves composition of morphisms. -/
private theorem pairMap_comp {a b c : A.obj} (f : a ⟶ b) (g : b ⟶ c) :
    pairMap F G (f ≫ g) = pairMap F G f ≫ pairMap F G g := sorry

/-- The total-category functor underlying the canonical pair. -/
private def pairFunctor :
    A.obj ⥤ (PseudoPullback (BasedCategory.toBase X) (BasedCategory.toBase Y)).obj where
  obj := pairObj F G
  map := pairMap F G
  map_id := pairMap_id F G
  map_comp := pairMap_comp F G

/-- The canonical pair retains the common base projection. -/
private theorem pairFunctor_comm :
    pairFunctor F G ⋙
        (PseudoPullback (BasedCategory.toBase X) (BasedCategory.toBase Y)).p = A.p := sorry

end Implementation

/-- Pair two based functors with common source into the relative product `X ×_C Y`. -/
@[stacks 0040 "pairing into a relative product"]
def pair (F : A ⥤ᵇ X) (G : A ⥤ᵇ Y) :
    A ⥤ᵇ PseudoPullback (BasedCategory.toBase X) (BasedCategory.toBase Y) where
  toFunctor := Implementation.pairFunctor F G
  w := Implementation.pairFunctor_comm F G

end PairImplementation

section PairComputations

variable (F : A ⥤ᵇ X) (G : A ⥤ᵇ Y)

/-- Pairing retains the source object's base object. -/
@[simp]
theorem pair.obj.base (a : A.obj) :
    baseObj ((pair F G).obj a) =
      A.p.obj a := sorry

/-- The first object projection of a pair is its image under the first functor. -/
@[simp]
theorem pair.obj.fst (a : A.obj) :
    fstObj ((pair F G).obj a) =
      F.obj a := sorry

/-- The second object projection of a pair is its image under the second functor. -/
@[simp]
theorem pair.obj.snd (a : A.obj) :
    sndObj ((pair F G).obj a) =
      G.obj a := sorry

/-- The full comparison isomorphism of a paired object is the equality transport between the
two base images of that object. This is the stable API for consumers that need both directions
of the comparison. -/
@[simp, stacks 0040 "paired object comparison isomorphism"]
theorem pair.obj.comparisonIso (a : A.obj) :
    comparisonIsoApp ((pair F G).obj a) =
      eqToIso ((F.w_obj a).trans (G.w_obj a).symm) := sorry

/-- The forward component of a paired object's comparison is the equality transport
between the two base images. -/
@[simp]
theorem pair.obj.comparisonIso.hom (a : A.obj) :
    (comparisonIsoApp ((pair F G).obj a)).hom =
      eqToHom ((F.w_obj a).trans (G.w_obj a).symm) := sorry

/-- The inverse component of a paired object's comparison is the reverse equality
transport between the two base images. -/
@[simp]
theorem pair.obj.comparisonIso.inv (a : A.obj) :
    (comparisonIsoApp ((pair F G).obj a)).inv =
      eqToHom ((G.w_obj a).trans (F.w_obj a).symm) := sorry

/-- The comparison morphism of a paired object is the forward equality transport between its
two base images. -/
@[simp]
theorem pair.obj.comparison (a : A.obj) :
    comparison ((pair F G).obj a) =
      eqToHom ((F.w_obj a).trans (G.w_obj a).symm) := sorry

/-- Pairing retains the source morphism's base map. -/
@[simp]
theorem pair.map.base {a b : A.obj} (f : a ⟶ b) :
    baseMap ((pair F G).map f) =
      A.p.map f := sorry

/-- The first morphism projection of a pair is its image under the first functor. -/
@[simp]
theorem pair.map.fst {a b : A.obj} (f : a ⟶ b) :
    fstMap ((pair F G).map f) =
      F.map f := sorry

/-- The second morphism projection of a pair is its image under the second functor. -/
@[simp]
theorem pair.map.snd {a b : A.obj} (f : a ⟶ b) :
    sndMap ((pair F G).map f) =
      G.map f := sorry

/-- A paired morphism satisfies the comparison square of its two component maps. -/
@[stacks 0040 "pairing comparison square"]
theorem pair.map.comm {a b : A.obj} (f : a ⟶ b) :
    CommSq
      ((BasedCategory.toBase X).map (F.map f))
      (comparison ((pair F G).obj a))
      (comparison ((pair F G).obj b))
      ((BasedCategory.toBase Y).map (G.map f)) := sorry

/-- The comparison arrows of paired objects are natural in source morphisms. -/
@[reassoc, stacks 0040 "pairing comparison naturality"]
theorem pair.map.naturality {a b : A.obj} (f : a ⟶ b) :
    (BasedCategory.toBase X).map (F.map f) ≫
        comparison ((pair F G).obj b) =
      comparison ((pair F G).obj a) ≫
        (BasedCategory.toBase Y).map (G.map f) := sorry

/-- The inverse comparison arrows of paired objects are natural in the reverse orientation. -/
@[reassoc, stacks 0040 "pairing inverse comparison naturality"]
theorem pair.map.invNaturality {a b : A.obj} (f : a ⟶ b) :
    (comparisonIsoApp ((pair F G).obj a)).inv ≫
        (BasedCategory.toBase X).map (F.map f) =
      (BasedCategory.toBase Y).map (G.map f) ≫
        (comparisonIsoApp ((pair F G).obj b)).inv := sorry

/-- The first projection of the canonical pair is the first input functor. -/
@[simp]
theorem pair.fst :
    pair F G ⋙ fst (BasedCategory.toBase X) (BasedCategory.toBase Y) = F := sorry

/-- The second projection of the canonical pair is the second input functor. -/
@[simp]
theorem pair.snd :
    pair F G ⋙ snd (BasedCategory.toBase X) (BasedCategory.toBase Y) = G := sorry

end PairComputations

end BasedCategory.PseudoPullback
end CategoryTheory
