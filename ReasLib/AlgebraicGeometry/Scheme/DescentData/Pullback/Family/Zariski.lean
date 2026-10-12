/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Zariski
public import ReasLib.CategoryTheory.Sites.Family.Covering
public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Pullback.Family.FullyFaithful

/-!
# Zariski descent along refinements of families

A same-base refinement of fixed-target scheme families induces an equivalence on descent data
when every fiber is a Zariski covering family. As a consequence, schemes over a base are
equivalent to descent data for any Zariski covering family of that base.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry.Scheme.DescentData.Pullback

variable {S : Scheme.{u}}
variable {𝒰 : SemiRepresentableFamily.Over.{v} S}
variable {𝒱 : SemiRepresentableFamily.Over.{w} S}

/-- A same-target refinement whose fiber over every target member is a Zariski covering induces
an equivalence on categories of scheme descent data. -/
theorem isEquivalenceOfZariskiFibers
    (φ : SemiRepresentableFamily.Over.Hom
      (SemiRepresentableFamily.Over.map (Over.map (𝟙 S)) 𝒰) 𝒱)
    (hzariski : ∀ j : 𝒱.index,
      SemiRepresentableFamily.Over.IsCovering Scheme.zariskiPrecoverage (φ.fiber j)) :
    (functorOfHom φ).IsEquivalence := sorry

end AlgebraicGeometry.Scheme.DescentData.Pullback

namespace AlgebraicGeometry.Scheme.DescentData

variable {S : Scheme.{u}}
variable {𝒰 : SemiRepresentableFamily.Over.{v} S}

/-- Restriction from schemes over a base to descent data for a Zariski covering family is an
equivalence. -/
theorem isEquivalenceOfZariskiCover
    (h𝒰 : SemiRepresentableFamily.Over.IsCovering Scheme.zariskiPrecoverage 𝒰) :
    (Scheme.overPseudofunctor.toDescentData
      (fun i : 𝒰.index ↦ (𝒰.obj i).hom)).IsEquivalence := sorry

end AlgebraicGeometry.Scheme.DescentData
