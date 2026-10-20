module

public import ReasLib.CategoryTheory.Sites.Family.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc
public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Pullback.Family
import ReasLib.AlgebraicGeometry.Scheme.DescentData.Pullback.FullyFaithful

/-!
# Full faithfulness of pullback along fiberwise fpqc refinements

A same-base refinement of fixed-target scheme families induces a fully faithful pullback
functor on descent data when every fiber is an fpqc covering family.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry.Scheme.DescentData.Pullback

variable {S : Scheme.{u}}
variable {𝒰 : SemiRepresentableFamily.Over.{v} S}
variable {𝒱 : SemiRepresentableFamily.Over.{w} S}

/-- Pullback of scheme descent data along a same-base family refinement is fully faithful
when the fiber over every target component is an fpqc covering family. -/
theorem fullyFaithfulOfFpqcFibers
    (φ : SemiRepresentableFamily.Over.Hom
      (SemiRepresentableFamily.Over.map (Over.map (𝟙 S)) 𝒰) 𝒱)
    (hfpqc : ∀ j : 𝒱.index, Scheme.FpqcCovering (φ.fiber j).obj) :
    Nonempty (functorOfHom φ).FullyFaithful := sorry

/-- Pullback of scheme descent data along a refinement between fpqc covering families is
fully faithful. -/
theorem fullyFaithfulOfFpqcRefinement
    (φ : SemiRepresentableFamily.Over.Hom
      (SemiRepresentableFamily.Over.map (Over.map (𝟙 S)) 𝒰) 𝒱)
    (h𝒰 : Scheme.FpqcCovering 𝒰.obj) (h𝒱 : Scheme.FpqcCovering 𝒱.obj) :
    Nonempty (functorOfHom φ).FullyFaithful := sorry

end AlgebraicGeometry.Scheme.DescentData.Pullback
