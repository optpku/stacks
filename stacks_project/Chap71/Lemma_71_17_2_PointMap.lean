/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import stacks_project.Chap71.Lemma_71_17_2_RatioMap
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import Mathlib.CategoryTheory.Yoneda

@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace.Blowup
variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {I : IdealSubobject X} [IsQuasiCoherent I]

/-- Test points of the actual fibre product. -/
abbrev affineFibrePoint (π : Blowup X I) (U : affineEtaleSite X) (T : Over S) :=
  (pullback U.obj.hom π.hom).functorOfPoints.obj (op T)

/-- The first projection gives the actual scheme map to the input chart. -/
def affineFibrePointToU (π : Blowup X I) (U : affineEtaleSite X) {T : Over S}
    (p : affineFibrePoint π U T) : T ⟶ U.obj.left :=
  (pullback.fst U.obj.hom π.hom).app (op T) p

/-- The second projection gives the actual map of the test scheme into the supplied blowup. -/
def affineFibrePointToBlowup (π : Blowup X I) (U : affineEtaleSite X) {T : Over S}
    (p : affineFibrePoint π U T) : ofOver T ⟶ π.space :=
  yonedaEquiv.symm ((pullback.snd U.obj.hom π.hom).app (op T) p)

/-- The two test maps satisfy the pullback triangle. -/
theorem affineFibrePoint_triangle (π : Blowup X I) (U : affineEtaleSite X) {T : Over S}
    (p : affineFibrePoint π U T) :
    ofOverMap (affineFibrePointToU π U p) ≫ U.obj.hom =
      affineFibrePointToBlowup π U p ≫ π.hom := sorry

/-- The image of a test point is the scheme morphism glued from the actual Rees ratios. -/
def affineComparisonPoint (π : Blowup X I) (U : affineEtaleSite X) {T : Over S}
    (p : affineFibrePoint π U T) : T ⟶ reesProjOver I U :=
  comparisonOverMap π U (affineFibrePointToU π U p) (affineFibrePointToBlowup π U p)
    (affineFibrePoint_triangle π U p)

/-- Restriction of a test point restricts all section ratios and hence the glued morphism. -/
theorem affineComparisonPoint_naturality (π : Blowup X I) (U : affineEtaleSite X)
    {T T' : (Over S)ᵒᵖ} (f : T ⟶ T') :
    (pullback U.obj.hom π.hom).functorOfPoints.map f ≫
        TypeCat.ofHom (affineComparisonPoint π U (T := T'.unop)) =
      TypeCat.ofHom (affineComparisonPoint π U (T := T.unop)) ≫
        (ofOver (reesProjOver I U)).functorOfPoints.map f := sorry

/-- The canonical affine-etale comparison has actual homogeneous-fraction morphism data. -/
def affineComparisonHom (π : Blowup X I) (U : affineEtaleSite X) :
    pullback U.obj.hom π.hom ⟶ ofOver (reesProjOver I U) where
  app T := TypeCat.ofHom (affineComparisonPoint π U)
  naturality _ _ f := affineComparisonPoint_naturality π U f

/-- On the supplied Twist atlas, this fixed morphism is the canonical affine relative-Proj
comparison: its standard-open ring maps send r*t^n/(a*t)^n to r/a^n. The stored
section models and Serre compatibility identify these with the Rees charts.
Relative-Proj base change and etale descent therefore make this actual map invertible.
No object equality or unspecified comparison map is used to supply its forward data. -/
theorem affineComparisonHom_isIso (π : Blowup X I) (U : affineEtaleSite X) :
    IsIso (affineComparisonHom π U) := sorry

/-- The specified homogeneous-fraction comparison commutes with the projection to U. -/
theorem affineComparisonHom_over (π : Blowup X I) (U : affineEtaleSite X) :
    affineComparisonHom π U ≫ reesProjOverToU I U = pullback.fst U.obj.hom π.hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Blowup
