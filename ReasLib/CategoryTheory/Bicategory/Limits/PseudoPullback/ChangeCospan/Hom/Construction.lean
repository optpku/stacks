module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Modification.Category
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ChangeCospan.Presentation.Construction
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Hom.Construction
public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoCone.Postcompose.Hom

/-!
# Constructors for changed-cospan cone morphisms

This leaf owns the concrete `fac`, `map`, and `map₂` data.  It deliberately contains no public
projection equations; those are kept in `Hom.Computations` so constructor-only consumers do not
load the readout surface.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory
open scoped CategoryTheory.Bicategory.CospanTransform

universe w v u

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Bicategory.PseudoPullbackCone

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z x' y' z' : B}
variable {f : x ⟶ z} {g : y ⟶ z} {f' : x' ⟶ z'} {g' : y' ⟶ z'}

namespace Implementation

/-- Component of the comparison carried by a readable cone morphism after changing cospan.
It conjugates generic pseudocone postcomposition by the explicit readable/generic presentation
comparisons at the source and target cones. -/
private def changeCospan.facApp
    (ψ : CospanTransform f g f' g')
    {S T : PseudoPullbackCone f g} (u : S ⟶ T)
    (j : LocallyDiscrete Limits.WalkingCospan) :
    PseudoPullbackCone.map u ≫
        (T.changeCospan ψ).toPseudoCone.π.app j ⟶
      (S.changeCospan ψ).toPseudoCone.π.app j :=
  PseudoPullbackCone.map u ◁
        (changeCospan.presentation.iso T ψ j).hom ≫
    (PseudoCone.postcomposeFac ψ u.hom).as.app j ≫
    (changeCospan.presentation.iso S ψ j).inv

/-- The conjugated generic postcomposition components satisfy modification naturality for
readable changed-cospan cones. -/
private theorem changeCospan.facApp_naturality
    (ψ : CospanTransform f g f' g')
    {S T : PseudoPullbackCone f g} (u : S ⟶ T) :
    ∀ {a b : LocallyDiscrete Limits.WalkingCospan} (h : a ⟶ b),
      (Pseudofunctor.const
          (LocallyDiscrete Limits.WalkingCospan) S.pt).map h ◁
            changeCospan.facApp ψ u b ≫
          ((S.changeCospan ψ).toPseudoCone.π.naturality h).hom =
        ((((T.changeCospan ψ).toPseudoCone.comparison S.pt).obj
            (PseudoPullbackCone.map u)).naturality h).hom ≫
          changeCospan.facApp ψ u a ▷
            (Bicategory.cospan f' g').map h := sorry

end Implementation

/-!
The comparison modification is the readable presentation of the generic postcomposition
comparison. Its component assembly is private to this construction owner.
-/

/-- The comparison modification carried by a readable cone morphism after changing cospan.

This is the generic `PseudoCone.postcomposeFac` comparison conjugated by the canonical
readable/generic presentation isomorphisms.  The component helper and its naturality law are
kept in this construction owner so a constructor-only import remains self-contained.
-/
def changeCospan.fac
    (ψ : CospanTransform f g f' g')
    {S T : PseudoPullbackCone f g} (u : S ⟶ T) :
    ((T.changeCospan ψ).toPseudoCone.comparison S.pt).obj
        (PseudoPullbackCone.map u) ⟶
      (S.changeCospan ψ).toPseudoCone.π :=
  ⟨{
    app := Implementation.changeCospan.facApp ψ u
    naturality := Implementation.changeCospan.facApp_naturality ψ u }⟩

/- A changed-cospan morphism is obtained from the unchanged apex map and the comparison above. -/

/-- A morphism of readable pseudo-pullback cones induces a morphism after changing the cospan.
Its apex map is unchanged.
-/
def changeCospan.map
    (ψ : CospanTransform f g f' g')
    {S T : PseudoPullbackCone f g} (u : S ⟶ T) :
    S.changeCospan ψ ⟶ T.changeCospan ψ :=
  PseudoPullbackCone.homMk
    (PseudoPullbackCone.map u : S.pt ⟶ T.pt) (changeCospan.fac ψ u)

namespace Implementation

/-- Compatibility of an unchanged apex cell with changed-cospan cone comparisons. -/
private theorem changeCospan.map₂_comm
    (ψ : CospanTransform f g f' g')
    {S T : PseudoPullbackCone f g} {u v : S ⟶ T} (η : u ⟶ v) :
    ((T.changeCospan ψ).toPseudoCone.comparison S.pt).map
          (PseudoPullbackCone.map₂ η) ≫
        PseudoPullbackCone.fac (changeCospan.map ψ v) =
      PseudoPullbackCone.fac (changeCospan.map ψ u) := sorry

end Implementation

/-- A `2`-morphism of readable pseudo-pullback cones induces a `2`-morphism after changing
cospan. Its apex cell is unchanged.
-/
def changeCospan.map₂
    (ψ : CospanTransform f g f' g')
    {S T : PseudoPullbackCone f g} {u v : S ⟶ T} (η : u ⟶ v) :
    changeCospan.map ψ u ⟶ changeCospan.map ψ v :=
  PseudoPullbackCone.hom₂Mk
    (PseudoPullbackCone.map₂ η :
      PseudoPullbackCone.map u ⟶ PseudoPullbackCone.map v)
    (Implementation.changeCospan.map₂_comm ψ η)

/- Data audit (mathlib 4.32): `fac`, `map`, and `map₂` retain the supplied comparison
modification or apex cell explicitly.  Their only deferred content is the compatibility field
needed by the generic readable-cone constructors; no apex object, map, or cell is selected by a
placeholder. -/

end Bicategory.PseudoPullbackCone

end CategoryTheory
