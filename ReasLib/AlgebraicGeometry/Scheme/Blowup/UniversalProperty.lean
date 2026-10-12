/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic

/-!
# The categorical universal property of a blowup

A blowup is the terminal scheme over its base among those on which the pulled-back center is an
effective Cartier divisor.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The full subcategory of schemes over `X` on which the pullback of the closed subscheme
defined by `I` is an effective Cartier divisor. -/
abbrev effectiveCartierPullbackOverCategory (X : Scheme.{u}) (I : X.IdealSheafData) :=
  ObjectProperty.FullSubcategory
    (fun Y : Over X ↦ IsEffectiveCartierDivisor (I.comap Y.hom).subschemeι)

namespace effectiveCartierPullbackOverCategory

/-- A blowup morphism regarded as an object over its base with effective-Cartier pullback of its
center. -/
def blowupObject {X X' : Scheme.{u}} (I : X.IdealSheafData)
    (b : X' ⟶ X) [h : IsBlowup b I] : effectiveCartierPullbackOverCategory X I :=
  ObjectProperty.FullSubcategory.mk (Over.mk b) h.toIsEffectiveCartierDivisor

/-- A blowup is terminal among schemes over its base on which the pulled-back center is an
effective Cartier divisor. -/
noncomputable def blowupObjectIsTerminal {X X' : Scheme.{u}} (I : X.IdealSheafData)
    (b : X' ⟶ X) [IsBlowup b I] : IsTerminal (blowupObject I b) :=
  IsTerminal.ofUniqueHom
    (fun Y ↦
      let h := IsBlowup.existsUnique_lift (I := I) (f := b) Y.obj.hom Y.property
      ObjectProperty.homMk (Over.homMk h.exists.choose h.exists.choose_spec))
    (fun Y m ↦ by
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      exact (IsBlowup.existsUnique_lift (I := I) (f := b) Y.obj.hom Y.property).unique
        m.hom.w
        (IsBlowup.existsUnique_lift (I := I) (f := b) Y.obj.hom Y.property).exists.choose_spec)

end effectiveCartierPullbackOverCategory

/-- The identity morphism is the blowup in an effective Cartier divisor. -/
@[stacks 0807 "identity blowup"]
instance instIsBlowupIdentity (X : Scheme.{u}) (I : X.IdealSheafData)
    [IsEffectiveCartierDivisor I.subschemeι] : IsBlowup (𝟙 X) I := sorry

end AlgebraicGeometry
