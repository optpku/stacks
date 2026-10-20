module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Sheaves.LocalPredicate
public import Mathlib.Topology.Sheaves.PresheafOfFunctions
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Constant sheaves and discrete-valued continuous functions

This module provides the concrete comparison map from the canonical constant sheaf to the sheaf of
continuous maps into a discrete space. The comparison and its stalk maps are thin, reusable bridges.

## Main declarations

- `TopCat.Presheaf.Constant.toDiscrete`: the comparison presheaf morphism
- `TopCat.Sheaf.Constant.toDiscrete`: the sheafified comparison (an iso)
- `TopCat.Presheaf.Constant.stalk_bijective`: the stalk of the constant presheaf is `A`
-/

@[expose] public section

open CategoryTheory Opposite TopCat TopologicalSpace

universe u

namespace TopCat.Presheaf.Constant

variable (X : TopCat.{u}) (A : Type u)

/-- The component map at an open `U`: sends `a : A` to the constant continuous map
from `U` into the discrete space on `A`. This extracts the repeated pattern to avoid
inline `ConcreteCategory.ofHom` annotations. -/
def componentMap (U : Opens X) : A → (presheafToTop X (TopCat.discrete.obj A)).obj (op U) :=
  fun a => ConcreteCategory.ofHom (C := TopCat) (ContinuousMap.const
    (β := TopCat.discrete.obj A) (Opens.toTopCat X |>.obj U) a)

/-- Naturality of the component maps: restriction commutes with the constant-map construction. -/
theorem componentMap_naturality {Y Z : (Opens X)ᵒᵖ} (i : Y ⟶ Z) :
    ((Functor.const (Opens X)ᵒᵖ).obj A).map i ≫ (↾componentMap X A Z.unop) =
      (↾componentMap X A Y.unop) ≫ (presheafToTop X (TopCat.discrete.obj A)).map i := sorry

/-- The natural transformation from the constant presheaf on `A` to the presheaf of continuous
maps into the discrete space on `A`. -/
def toDiscrete : (Functor.const (Opens X)ᵒᵖ).obj A ⟶ presheafToTop X (TopCat.discrete.obj A) where
  app Y := ↾componentMap X A Y.unop
  naturality := fun {_ _} i => componentMap_naturality X A i

/-- The global germ map identifies `A` with the stalk of the constant presheaf. -/
theorem stalk_bijective (x : X) :
    Function.Bijective (Presheaf.Γgerm ((Functor.const (Opens X)ᵒᵖ).obj A) x) := sorry

/-- The global germ map of the constant presheaf is an isomorphism. -/
instance stalk_isIso (x : X) :
    IsIso (Presheaf.Γgerm ((Functor.const (Opens X)ᵒᵖ).obj A) x) := sorry

/-- Restriction in the discrete-valued continuous-function presheaf is precomposition with the
inclusion of opens. -/
theorem discreteContinuous_restrict_apply {X : TopCat.{u}} {A : Type u}
    {U V : Opens X} (hUV : U ≤ V)
    (f : (presheafToTop X (TopCat.discrete.obj A)).obj (op V)) (x : U) :
    (ConcreteCategory.hom
      (ConcreteCategory.hom ((presheafToTop X (TopCat.discrete.obj A)).map (homOfLE hUV).op) f)) x =
      (ConcreteCategory.hom f) (homOfLE hUV x) := sorry

end TopCat.Presheaf.Constant

namespace TopCat.Sheaf.Constant

variable (X : TopCat.{u}) (A : Type u)

/-- The canonical comparison from the constant sheaf to the sheaf of continuous maps into the
discrete space on `A`. -/
noncomputable def toDiscrete :
    (CategoryTheory.constantSheaf (Opens.grothendieckTopology X) (Type u)).obj A ⟶
      sheafToTop (TopCat.discrete.obj A) :=
  Sheaf.homEquiv.symm <|
    sheafifyLift (Opens.grothendieckTopology X)
      (TopCat.Presheaf.Constant.toDiscrete X A) (sheafToTop (TopCat.discrete.obj A)).property

/-- The comparison from the constant sheaf to discrete-valued continuous functions is an iso. -/
instance toDiscrete_isIso : IsIso (toDiscrete X A) := sorry

/-- The canonical map from `A` to the stalk of its constant sheaf. -/
noncomputable def toStalk (x : X) :
    A ⟶ Presheaf.stalk
      ((CategoryTheory.constantSheaf (Opens.grothendieckTopology X) (Type u)).obj A).obj x :=
  Presheaf.Γgerm ((Functor.const (Opens X)ᵒᵖ).obj A) x ≫
    (Presheaf.stalkFunctor (Type u) x).map
      (CategoryTheory.toSheafify
        (Opens.grothendieckTopology X) ((Functor.const (Opens X)ᵒᵖ).obj A))

/-- The canonical map to the constant-sheaf stalk is an isomorphism. -/
instance toStalk_isIso (x : X) : IsIso (toStalk X A x) := sorry

end TopCat.Sheaf.Constant

end
