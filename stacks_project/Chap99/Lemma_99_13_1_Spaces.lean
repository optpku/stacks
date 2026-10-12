/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.CategoryTheory.Fibered.StronglyCartesianSubcategory
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap95.«95_7_0_1_Spaces»

/-!
# Finite-type and fp-flat-proper groupoids of algebraic spaces

The primed categories `Spaces'_ft` and `Spaces'_{fp, flat, proper}` of algebraic
spaces over schemes over a base, with morphisms the cartesian squares.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces is of finite presentation, flat, and proper.
The parent classes `FinitePresentation`, `Flat`, and `Proper` cannot be
extended simultaneously: `Flat` and `LocallyOfFinitePresentation` both own an
`of_etale` field. -/
@[mk_iff]
class FpFlatProper {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop where
  /-- The morphism is of finite presentation. -/
  finitePresentation : FinitePresentation f
  /-- The morphism is flat. -/
  flat : Flat f
  /-- The morphism is proper. -/
  proper : Proper f

namespace FpFlatProper

/-- An `FpFlatProper` morphism is of finite presentation, flat, and proper. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [FpFlatProper f] : FinitePresentation f ∧ Flat f ∧ Proper f := sorry

/-- An `FpFlatProper` morphism is of finite presentation. -/
instance toFinitePresentation {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [h : FpFlatProper f] : FinitePresentation f :=
  h.finitePresentation

/-- An `FpFlatProper` morphism is flat. -/
instance toFlat {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [h : FpFlatProper f] : Flat f :=
  h.flat

/-- An `FpFlatProper` morphism is proper. -/
instance toProper {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [h : FpFlatProper f] : Proper f :=
  h.proper

/-- The identity morphism of an algebraic space is of finite presentation, flat,
and proper. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : FpFlatProper (𝟙 X) where
  finitePresentation := inferInstance
  flat := inferInstance
  proper := inferInstance

/-- An isomorphism of algebraic spaces is of finite presentation, flat, and
proper. -/
instance of_isIso {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsIso f] : FpFlatProper f := sorry

/-- A finite-presentation, flat, and proper morphism of algebraic spaces is
`FpFlatProper`. -/
instance instOfFinitePresentationFlatProper {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [FinitePresentation f] [Flat f]
    [Proper f] : FpFlatProper f where
  finitePresentation := inferInstance
  flat := inferInstance
  proper := inferInstance

end FpFlatProper

namespace Spaces

/-- Objects of `Spaces S` whose structure morphism is of finite type. -/
def finiteType (S : Scheme.{u}) : ObjectProperty (Spaces S) :=
  fun P ↦ FiniteType P.hom

/-- Membership in `finiteType S` is finite type of the structure morphism. -/
theorem finiteType_iff {S : Scheme.{u}} (P : Spaces S) :
    finiteType S P ↔ FiniteType P.hom := sorry

/-- Finite type of structure morphisms is preserved by cartesian squares in
`Spaces`. -/
theorem finiteType_of_isPullback {S : Scheme.{u}} {P Q : Spaces S} (φ : P ⟶ Q)
    (hφ : IsPullback φ.left P.hom Q.hom ((ofOverFunctor S).map φ.right))
    (hQ : finiteType S Q) : finiteType S P := sorry

/-- The primed category of finite-type algebraic spaces over schemes over `S`,
with morphisms the strongly cartesian squares. -/
abbrev FtGroupoids (S : Scheme.{u}) :=
  Functor.IsStronglyCartesian.subcategory ((finiteType S).ι ⋙ p)

/-- `FtGroupoids S` is the strongly cartesian wide subcategory of the finite-type
full subcategory of `Spaces S`. -/
theorem FtGroupoids_eq (S : Scheme.{u}) :
    FtGroupoids S =
      Functor.IsStronglyCartesian.subcategory ((finiteType S).ι ⋙ p) := sorry

/-- The projection `FtGroupoids S ⥤ Over S`. -/
abbrev pFtGroupoids (S : Scheme.{u}) : FtGroupoids S ⥤ Over S :=
  Functor.IsStronglyCartesian.projection ((finiteType S).ι ⋙ p)

/-- `pFtGroupoids S` is the strongly cartesian restricted projection of the
finite-type forgetful functor. -/
theorem pFtGroupoids_eq (S : Scheme.{u}) :
    pFtGroupoids S =
      Functor.IsStronglyCartesian.projection ((finiteType S).ι ⋙ p) := sorry

namespace FtGroupoids

/-- Package a finite-type morphism `X ⟶ ofOver U` as an object of
`FtGroupoids S`. -/
def mk {S : Scheme.{u}} {U : Over S} {X : AlgebraicSpace S}
    (pX : X ⟶ ofOver U) [FiniteType pX] : FtGroupoids S :=
  { obj := { obj := Spaces.mk pX, property := (inferInstance : FiniteType pX) } }

/-- The underlying `Spaces` object of `mk pX` is `Spaces.mk pX`. -/
theorem mk_obj {S : Scheme.{u}} {U : Over S} {X : AlgebraicSpace S}
    (pX : X ⟶ ofOver U) [FiniteType pX] :
    (mk pX).obj.obj = Spaces.mk pX := sorry

/-- The structure morphism of `mk pX` is `pX`. -/
theorem mk_hom {S : Scheme.{u}} {U : Over S} {X : AlgebraicSpace S}
    (pX : X ⟶ ofOver U) [FiniteType pX] : (mk pX).obj.obj.hom = pX := sorry

/-- The identity of `ofOver U` as a finite-type object of `FtGroupoids`. -/
def ofId (S : Scheme.{u}) (U : Over S) : FtGroupoids S :=
  mk (𝟙 (ofOver U))

/-- `ofId S U` is `mk` of the identity of `ofOver U`. -/
theorem ofId_eq (S : Scheme.{u}) (U : Over S) :
    ofId S U = mk (𝟙 (ofOver U)) := sorry

/-- A morphism of `FtGroupoids` is a cartesian square of algebraic spaces. -/
theorem hom_isPullback {S : Scheme.{u}} {P Q : FtGroupoids S} (φ : P ⟶ Q) :
    IsPullback φ.hom.hom.left P.obj.obj.hom Q.obj.obj.hom
      ((ofOverFunctor S).map φ.hom.hom.right) := sorry

end FtGroupoids

/-- The projection `pFtGroupoids` sends `mk pX` to the scheme `U` over `S`. -/
theorem pFtGroupoids_obj {S : Scheme.{u}} {U : Over S} {X : AlgebraicSpace S}
    (pX : X ⟶ ofOver U) [FiniteType pX] :
    (pFtGroupoids S).obj (FtGroupoids.mk pX) = U := sorry

/-- Objects of `FtGroupoids S` whose structure morphism is of finite
presentation, flat, and proper. -/
def fpFlatProper (S : Scheme.{u}) : ObjectProperty (FtGroupoids S) :=
  fun P ↦ FpFlatProper P.obj.obj.hom

/-- Membership in `fpFlatProper S` is `FpFlatProper` of the structure
morphism. -/
theorem fpFlatProper_iff {S : Scheme.{u}} (P : FtGroupoids S) :
    fpFlatProper S P ↔ FpFlatProper P.obj.obj.hom := sorry

/-- The full subcategory of `FtGroupoids S` on finite-presentation, flat, and
proper structure morphisms. -/
abbrev FpFlatProperGroupoids (S : Scheme.{u}) :=
  (fpFlatProper S).FullSubcategory

/-- `FpFlatProperGroupoids S` is the `fpFlatProper` full subcategory of
`FtGroupoids S`. -/
theorem FpFlatProperGroupoids_eq (S : Scheme.{u}) :
    FpFlatProperGroupoids S = (fpFlatProper S).FullSubcategory := sorry

/-- The projection `FpFlatProperGroupoids S ⥤ Over S`, obtained by restricting
`pFtGroupoids`. -/
abbrev pFpFlatProperGroupoids (S : Scheme.{u}) :
    FpFlatProperGroupoids S ⥤ Over S :=
  (fpFlatProper S).ι ⋙ pFtGroupoids S

/-- `pFpFlatProperGroupoids S` is the composite of the full-subcategory
inclusion with `pFtGroupoids S`. -/
theorem pFpFlatProperGroupoids_eq (S : Scheme.{u}) :
    pFpFlatProperGroupoids S = (fpFlatProper S).ι ⋙ pFtGroupoids S := sorry

namespace FpFlatProperGroupoids

/-- Package an `FpFlatProper` morphism `X ⟶ ofOver U` as an object of
`FpFlatProperGroupoids S`. -/
def mk {S : Scheme.{u}} {U : Over S} {X : AlgebraicSpace S}
    (pX : X ⟶ ofOver U) [FpFlatProper pX] : FpFlatProperGroupoids S :=
  { obj := FtGroupoids.mk pX, property := (inferInstance : FpFlatProper pX) }

/-- The underlying `FtGroupoids` object of `mk pX` is `FtGroupoids.mk pX`. -/
theorem mk_obj {S : Scheme.{u}} {U : Over S} {X : AlgebraicSpace S}
    (pX : X ⟶ ofOver U) [FpFlatProper pX] :
    (mk pX).obj = FtGroupoids.mk pX := sorry

/-- The identity of `ofOver U` as an fp-flat-proper object of
`FpFlatProperGroupoids`. -/
def ofId (S : Scheme.{u}) (U : Over S) : FpFlatProperGroupoids S :=
  mk (𝟙 (ofOver U))

/-- `ofId S U` is `mk` of the identity of `ofOver U`. -/
theorem ofId_eq (S : Scheme.{u}) (U : Over S) :
    ofId S U = mk (𝟙 (ofOver U)) := sorry

/-- The full-subcategory inclusion
`FpFlatProperGroupoids S ⥤ FtGroupoids S`. -/
abbrev inclusion (S : Scheme.{u}) :
    FpFlatProperGroupoids S ⥤ FtGroupoids S :=
  (fpFlatProper S).ι

/-- The inclusion of `FpFlatProperGroupoids` is full. -/
instance inclusion_full (S : Scheme.{u}) : (inclusion S).Full :=
  inferInstance

/-- The inclusion of `FpFlatProperGroupoids` is faithful. -/
instance inclusion_faithful (S : Scheme.{u}) : (inclusion S).Faithful :=
  inferInstance

/-- The inclusion sends `mk pX` to `FtGroupoids.mk pX`. -/
theorem inclusion_obj {S : Scheme.{u}} {U : Over S} {X : AlgebraicSpace S}
    (pX : X ⟶ ofOver U) [FpFlatProper pX] :
    (inclusion S).obj (mk pX) = FtGroupoids.mk pX := sorry

end FpFlatProperGroupoids

/-- The projection `pFpFlatProperGroupoids` sends `mk pX` to the scheme `U`
over `S`. -/
theorem pFpFlatProperGroupoids_obj {S : Scheme.{u}} {U : Over S}
    {X : AlgebraicSpace S} (pX : X ⟶ ofOver U) [FpFlatProper pX] :
    (pFpFlatProperGroupoids S).obj (FpFlatProperGroupoids.mk pX) = U := sorry

/-- Finite presentation, flatness, and properness of structure morphisms are
preserved by cartesian squares in `FtGroupoids`. -/
theorem fpFlatProper_of_isPullback {S : Scheme.{u}} {P Q : FtGroupoids S}
    (φ : P ⟶ Q)
    (hφ : IsPullback φ.hom.hom.left P.obj.obj.hom Q.obj.obj.hom
      ((ofOverFunctor S).map φ.hom.hom.right))
    (hQ : fpFlatProper S Q) : fpFlatProper S P := sorry

end Spaces

end AlgebraicGeometry.AlgebraicSpace

