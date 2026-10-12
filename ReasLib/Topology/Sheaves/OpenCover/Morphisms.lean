/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaves.OpenCover.Gluing

/-!
# Morphisms glued from an open cover

This module owns the cover-indexed form of the local-morphism condition for sheaves.  It uses the
generic `IsOpenEmbedding.sheafPullback` restrictions already owned by the open-cover gluing API,
so it applies to arbitrary coefficient categories and does not introduce a second pullback model.
-/

@[expose] public section

open CategoryTheory TopCat TopologicalSpace
open TopologicalSpace.Opens

noncomputable section

universe u v w

namespace TopCat.Sheaf.OpenCover

variable {X : TopCat.{u}} {C : Type v} [Category.{u} C]
variable {ι : Type w}

/-- A family of morphisms between the restrictions of two `C`-valued sheaves to an indexed open
family. -/
abbrev LocalHom (U : ι → Opens X) (F G : TopCat.Sheaf C X) :=
  ∀ i,
    (restrictToOpen (C := C) (U i)).obj F ⟶
      (restrictToOpen (C := C) (U i)).obj G

namespace LocalHom

/-- Restrict the local component on the left chart to the pairwise overlap. -/
noncomputable def restrictToOverlapLeft
    (U : ι → Opens X) {F G : TopCat.Sheaf C X} (phi : LocalHom U F G)
    (i j : ι) :
    (restrictToOpen (C := C) (U i ⊓ U j)).obj F ⟶
      (restrictToOpen (C := C) (U i ⊓ U j)).obj G :=
  (globalRestrictionToPairViaLeftIso (C := C) (U i) (U j)).hom.app F ≫
    (restrictToPairLeft (C := C) (U i) (U j)).map (phi i) ≫
      (globalRestrictionToPairViaLeftIso (C := C) (U i) (U j)).inv.app G

/-- Restrict the local component on the right chart to the pairwise overlap. -/
noncomputable def restrictToOverlapRight
    (U : ι → Opens X) {F G : TopCat.Sheaf C X} (phi : LocalHom U F G)
    (i j : ι) :
    (restrictToOpen (C := C) (U i ⊓ U j)).obj F ⟶
      (restrictToOpen (C := C) (U i ⊓ U j)).obj G :=
  (globalRestrictionToPairViaRightIso (C := C) (U i) (U j)).hom.app F ≫
    (restrictToPairRight (C := C) (U i) (U j)).map (phi j) ≫
      (globalRestrictionToPairViaRightIso (C := C) (U i) (U j)).inv.app G

/-- A local family of sheaf morphisms agrees after restriction to every pairwise overlap. -/
def IsCompatible (U : ι → Opens X) (F G : TopCat.Sheaf C X)
    (phi : LocalHom U F G) : Prop :=
  ∀ i j, restrictToOverlapLeft U phi i j = restrictToOverlapRight U phi i j

/-- A local family of morphisms together with its pairwise-overlap compatibility. -/
abbrev CompatibleLocalHom (U : ι → Opens X) (F G : TopCat.Sheaf C X) :=
  { phi : LocalHom U F G // IsCompatible U F G phi }

/-- An overlap-compatible local family defines a morphism between the canonical gluing data of
the two ambient sheaves. -/
noncomputable def toGluingHom
    (U : ι → Opens X) {F G : TopCat.Sheaf C X}
    (phi : CompatibleLocalHom U F G) :
    Gluing.Hom (Gluing.ofSheaf U F) (Gluing.ofSheaf U G) where
  hom := phi.1
  comm := sorry

/-- A morphism between canonical gluing data gives an overlap-compatible local family. -/
def ofGluingHom
    (U : ι → Opens X) {F G : TopCat.Sheaf C X}
    (f : Gluing.Hom (Gluing.ofSheaf U F) (Gluing.ofSheaf U G)) :
    CompatibleLocalHom U F G :=
  ⟨f.hom, sorry⟩

/-- Translating a compatible local family to canonical gluing data and back is the identity. -/
@[simp]
theorem ofGluingHom_toGluingHom
    (U : ι → Opens X) {F G : TopCat.Sheaf C X}
    (phi : CompatibleLocalHom U F G) :
    ofGluingHom U (toGluingHom U phi) = phi := sorry

/-- Translating a morphism of canonical gluing data to a compatible local family and back is the
identity. -/
@[simp]
theorem toGluingHom_ofGluingHom
    (U : ι → Opens X) {F G : TopCat.Sheaf C X}
    (f : Gluing.Hom (Gluing.ofSheaf U F) (Gluing.ofSheaf U G)) :
    toGluingHom U (ofGluingHom U f) = f := sorry

/-- Compatible local morphism families are exactly morphisms between the canonical gluing data
of the two ambient sheaves. -/
noncomputable def compatibleEquivOfSheafHom
    (U : ι → Opens X) (F G : TopCat.Sheaf C X) :
    CompatibleLocalHom U F G ≃ (Gluing.ofSheaf U F ⟶ Gluing.ofSheaf U G) where
  toFun := toGluingHom U
  invFun := ofGluingHom U
  left_inv := ofGluingHom_toGluingHom U
  right_inv := toGluingHom_ofGluingHom U

/-- Restrict a global morphism of sheaves to every member of an indexed open family. -/
def restrict (U : ι → Opens X) {F G : TopCat.Sheaf C X} (f : F ⟶ G) :
    LocalHom U F G :=
  fun i ↦ (restrictToOpen (C := C) (U i)).map f

/-- The local restrictions of a global sheaf morphism agree on every pairwise overlap. -/
theorem restrict_isCompatible (U : ι → Opens X) {F G : TopCat.Sheaf C X} (f : F ⟶ G) :
    IsCompatible U F G (restrict U f) := sorry

/-- Restrict a global morphism as a compatible family on an indexed open family. -/
def restrictCompatible (U : ι → Opens X) {F G : TopCat.Sheaf C X} (f : F ⟶ G) :
    CompatibleLocalHom U F G :=
  ⟨restrict U f, restrict_isCompatible U f⟩

/-- Translating the restrictions of a global morphism to canonical gluing data recovers the
morphism induced by the restriction functor. -/
@[simp]
theorem toGluingHom_restrictCompatible
    (U : ι → Opens X) {F G : TopCat.Sheaf C X} (f : F ⟶ G) :
    toGluingHom U (restrictCompatible U f) = Gluing.ofSheafMap U f := sorry

/-- Compatible local morphism families over an open cover are canonically equivalent to global
morphisms of sheaves. This combines the local compatibility model with the full faithfulness of
the restriction-to-gluing-data functor. -/
noncomputable def globalHomEquiv
    (U : ι → Opens X) (hU : IsOpenCover U) (F G : TopCat.Sheaf C X) :
    CompatibleLocalHom U F G ≃ (F ⟶ G) :=
  (compatibleEquivOfSheafHom U F G).trans
    (Gluing.ofSheafFunctorHomEquiv U hU F G).symm

/-- The inverse of `globalHomEquiv` sends a global morphism to its compatible family of local
restrictions. -/
@[simp]
theorem globalHomEquiv_symm_apply
    (U : ι → Opens X) (hU : IsOpenCover U) (F G : TopCat.Sheaf C X) (f : F ⟶ G) :
    (globalHomEquiv U hU F G).symm f = restrictCompatible U f := sorry

/-- The global morphism associated to a compatible local family restricts to the specified local
morphism on every chart of the open cover. -/
@[simp]
theorem globalHomEquiv_apply_restrict
    (U : ι → Opens X) (hU : IsOpenCover U) (F G : TopCat.Sheaf C X)
    (phi : CompatibleLocalHom U F G) (i : ι) :
    (restrict U (globalHomEquiv U hU F G phi)) i = phi.1 i := sorry

/-- A compatible family of local morphisms over an open cover glues to a unique global morphism
of sheaves. -/
theorem existsUniqueGlobalHom
    (U : ι → Opens X) (hU : IsOpenCover U) (F G : TopCat.Sheaf C X)
    (phi : LocalHom U F G) (hphi : IsCompatible U F G phi) :
    ∃! f : F ⟶ G, ∀ i,
      (restrictToOpen (C := C) (U i)).map f = phi i := sorry

/-- A global sheaf morphism is determined by its restrictions to the members of an open cover. -/
theorem restrict_injective
    (U : ι → Opens X) (hU : IsOpenCover U) {F G : TopCat.Sheaf C X} :
    Function.Injective (fun f : F ⟶ G => restrict U f) := sorry

/-- Two global sheaf morphisms agree exactly when their restrictions to an open cover agree. -/
theorem restrict_eq_iff
    (U : ι → Opens X) (hU : IsOpenCover U) {F G : TopCat.Sheaf C X}
    (f g : F ⟶ G) :
    restrict U f = restrict U g ↔ f = g := sorry

end LocalHom

end TopCat.Sheaf.OpenCover

end
