/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Elements
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Spaces

/-!
# Étale neighborhoods of a geometric point of an algebraic space

An étale neighborhood of a geometric point `xbar` of an algebraic space `X` is an étale
morphism of algebraic spaces into `X` together with a chosen lift of `xbar`. Morphisms are
`X`-morphisms that preserve the chosen lifts.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

namespace GeometricPoint

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The functor on the étale slice of algebraic spaces over `X` sending `U` to the type of lifts
of a geometric point through `U.hom`. -/
abbrev etaleLiftFunctor (xbar : GeometricPoint X) : spacesEtaleSite X ⥤ Type (u + 1) :=
  MorphismProperty.Over.forget (@Etale S) ⊤ X ⋙ coyoneda.obj (op (Over.mk xbar.hom))

/-- The value of `etaleLiftFunctor xbar` at `U` is the type of morphisms in `Over X` from
`Over.mk xbar.hom` to the forgotten étale object. -/
theorem etaleLiftFunctor_obj (xbar : GeometricPoint X) (U : spacesEtaleSite X) :
    (etaleLiftFunctor xbar).obj U =
      (Over.mk xbar.hom ⟶ (MorphismProperty.Over.forget (@Etale S) ⊤ X).obj U) :=
  sorry

/-- The étale neighborhoods of a geometric point, represented by the category of elements of
the lift functor on the étale slice of algebraic spaces. -/
abbrev EtaleNeighborhood (xbar : GeometricPoint X) :=
  (etaleLiftFunctor xbar).Elements

/-- The category of étale neighborhoods is the category of elements of `etaleLiftFunctor`. -/
theorem etaleNeighborhood_eq (xbar : GeometricPoint X) :
    EtaleNeighborhood xbar = (etaleLiftFunctor xbar).Elements :=
  sorry

namespace EtaleNeighborhood

variable {xbar : GeometricPoint X}

/-- The object of the étale site of algebraic spaces underlying an étale neighborhood. -/
abbrev toSpacesEtale (U : EtaleNeighborhood xbar) : spacesEtaleSite X :=
  U.1

/-- The algebraic space underlying an étale neighborhood. -/
abbrev space (U : EtaleNeighborhood xbar) : AlgebraicSpace S :=
  U.toSpacesEtale.left

/-- The structure morphism of an étale neighborhood, as an étale morphism of algebraic spaces
into `X`. -/
abbrev hom (U : EtaleNeighborhood xbar) : U.space ⟶ X :=
  U.toSpacesEtale.hom

/-- The chosen lift of a geometric point to an étale neighborhood. -/
abbrev lift (U : EtaleNeighborhood xbar) : ofOver xbar.overObj ⟶ U.space :=
  U.2.left

/-- The chosen lift of a geometric point commutes with the étale structure morphism. -/
theorem lift_fac (U : EtaleNeighborhood xbar) : U.lift ≫ U.hom = xbar.hom :=
  sorry

/-- Reconstruct the geometric point of an étale neighborhood from its chosen lift, using the
same source field as `xbar`. -/
def geometricPoint (U : EtaleNeighborhood xbar) : GeometricPoint U.space where
  K := xbar.K
  structureHom := xbar.structureHom
  hom := U.lift
  isAlgClosed := xbar.isAlgClosed

/-- The morphism of `geometricPoint U` is the chosen lift. -/
@[simp]
theorem geometricPoint_hom (U : EtaleNeighborhood xbar) :
    (geometricPoint U).hom = U.lift :=
  sorry

/-- An étale neighborhood is an étale morphism of algebraic spaces together with a commuting
lift of the geometric point. -/
theorem spec (U : EtaleNeighborhood xbar) :
    Etale U.hom ∧ U.lift ≫ U.hom = xbar.hom :=
  sorry

/-- Construct an étale neighborhood from an étale algebraic space over `X` and a lift of the
geometric point. -/
def of (U : spacesEtaleSite X) (u : ofOver xbar.overObj ⟶ U.left)
    (hu : u ≫ U.hom = xbar.hom) : EtaleNeighborhood xbar :=
  Functor.elementsMk (etaleLiftFunctor xbar) U
    (Over.homMk u hu :
      Over.mk xbar.hom ⟶ (MorphismProperty.Over.forget (@Etale S) ⊤ X).obj U)

/-- The underlying étale object of `of U u hu` is `U`. -/
@[simp]
theorem of_toSpacesEtale (U : spacesEtaleSite X) (u : ofOver xbar.overObj ⟶ U.left)
    (hu : u ≫ U.hom = xbar.hom) : (of U u hu).toSpacesEtale = U :=
  sorry

/-- The underlying algebraic space of `of U u hu` is `U.left`. -/
@[simp]
theorem of_space (U : spacesEtaleSite X) (u : ofOver xbar.overObj ⟶ U.left)
    (hu : u ≫ U.hom = xbar.hom) : (of U u hu).space = U.left :=
  sorry

/-- The structure morphism of `of U u hu` is `U.hom`. -/
@[simp]
theorem of_hom (U : spacesEtaleSite X) (u : ofOver xbar.overObj ⟶ U.left)
    (hu : u ≫ U.hom = xbar.hom) : (of U u hu).hom = U.hom :=
  sorry

/-- The chosen lift of `of U u hu` is the supplied lift. -/
@[simp]
theorem of_lift (U : spacesEtaleSite X) (u : ofOver xbar.overObj ⟶ U.left)
    (hu : u ≫ U.hom = xbar.hom) : (of U u hu).lift = u :=
  sorry

/-- The identity étale neighborhood `(X, xbar)` with structure morphism `𝟙 X`. -/
def self (xbar : GeometricPoint X) : EtaleNeighborhood xbar :=
  of (MorphismProperty.Over.mk ⊤ (𝟙 X) inferInstance) xbar.hom (Category.comp_id _)

/-- The structure morphism of `self xbar` is the identity on `X`. -/
@[simp]
theorem self_hom (xbar : GeometricPoint X) : (self xbar).hom = 𝟙 X :=
  sorry

/-- The chosen lift of `self xbar` is `xbar.hom`. -/
@[simp]
theorem self_lift (xbar : GeometricPoint X) : (self xbar).lift = xbar.hom :=
  sorry

/-- A morphism of étale neighborhoods is a morphism in the category of elements, hence an
`X`-morphism preserving the chosen lifts. -/
abbrev Hom (V U : EtaleNeighborhood xbar) :=
  V ⟶ U

namespace Hom

/-- The morphism of étale algebraic spaces over `X` underlying a morphism of étale
neighborhoods. -/
abbrev toSpacesEtaleHom {V U : EtaleNeighborhood xbar} (f : Hom V U) :
    V.toSpacesEtale ⟶ U.toSpacesEtale :=
  f.val

/-- The morphism of algebraic spaces underlying a morphism of étale neighborhoods. -/
abbrev spaceHom {V U : EtaleNeighborhood xbar} (f : Hom V U) : V.space ⟶ U.space :=
  f.toSpacesEtaleHom.left

/-- A morphism of étale neighborhoods preserves the selected lifts. -/
theorem lift_fac {V U : EtaleNeighborhood xbar} (f : Hom V U) :
    V.lift ≫ f.spaceHom = U.lift :=
  sorry

/-- The underlying algebraic-space map of a morphism of étale neighborhoods is an `X`-morphism. -/
theorem over_fac {V U : EtaleNeighborhood xbar} (f : Hom V U) :
    f.spaceHom ≫ U.hom = V.hom :=
  sorry

/-- A morphism of étale neighborhoods is an `X`-morphism identifying the selected lifts. -/
theorem spec {V U : EtaleNeighborhood xbar} (f : Hom V U) :
    f.spaceHom ≫ U.hom = V.hom ∧ V.lift ≫ f.spaceHom = U.lift :=
  sorry

/-- Construct a morphism of étale neighborhoods from an étale `X`-morphism preserving the
selected lifts. -/
def of {V U : EtaleNeighborhood xbar} (f : V.toSpacesEtale ⟶ U.toSpacesEtale)
    (hf : V.lift ≫ f.left = U.lift) : Hom V U :=
  CategoryOfElements.homMk V U f (Over.OverMorphism.ext hf)

/-- The underlying étale morphism of `Hom.of f hf` is the supplied morphism. -/
@[simp]
theorem of_toSpacesEtaleHom {V U : EtaleNeighborhood xbar} (f : V.toSpacesEtale ⟶ U.toSpacesEtale)
    (hf : V.lift ≫ f.left = U.lift) : (of f hf).toSpacesEtaleHom = f :=
  sorry

/-- The underlying algebraic-space map of `Hom.of f hf` is the left component of the supplied
morphism. -/
@[simp]
theorem of_spaceHom {V U : EtaleNeighborhood xbar} (f : V.toSpacesEtale ⟶ U.toSpacesEtale)
    (hf : V.lift ≫ f.left = U.lift) : (of f hf).spaceHom = f.left :=
  sorry

end Hom

/-- Every étale covering of an étale neighborhood of a geometric point has a member admitting
a lift from the same geometric point, compatible with the structure map and the chosen lift
in the original neighborhood. -/
theorem exists_lift_of_cover
    {S : Scheme.{u}} {X : AlgebraicSpace S} (xbar : GeometricPoint X)
    (U : EtaleNeighborhood xbar)
    {I : Type v} (V : I → spacesEtaleSite X)
    (φ : ∀ i, V i ⟶ U.toSpacesEtale)
    (hcover : Sieve.ofArrows V φ ∈ spacesEtaleTopology X U.toSpacesEtale) :
    ∃ (i : I) (u_i : ofOver xbar.overObj ⟶ (V i).left),
      u_i ≫ (V i).hom = xbar.hom ∧ u_i ≫ (φ i).left = U.lift := sorry

end EtaleNeighborhood

end GeometricPoint

end AlgebraicGeometry.AlgebraicSpace
