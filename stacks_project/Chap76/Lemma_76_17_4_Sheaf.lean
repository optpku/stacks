/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap76.«76_17_4_1_Deformation»

/-!
# The sheaf of compatible local deformations of maps

Given first-order thickenings `X ⊂ X'` and `Y ⊂ Y'` over `B`, a map
`a : X ⟶ Y`, and an `𝒪_X`-linear comparison of conormal sheaves, the
compatible local lifts of `a` assemble into a sheaf of sets on
`X'_spaces,étale`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Deformation

variable {S : Scheme.{u}} {B X X' Y Y' : AlgebraicSpace S}

/-- The presheaf on `X'_spaces,étale` whose value at `U'` is the type of morphisms
`U'.left ⟶ Y'` compatible with the given first-order thickenings, the map `a`,
and the conormal comparison `A`. -/
noncomputable def sectionsPresheaf (sX' : X' ⟶ B) (sY' : Y' ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y)
    [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (A : (Modules.pullback a).obj (conormalSheaf iY) ⟶ conormalSheaf iX) :
    (spacesEtaleSite X')ᵒᵖ ⥤ Type (u + 1) where
  obj U' := { a' : U'.unop.left ⟶ Y' // a' ∈ sections sX' sY' iX iY a A U'.unop }
  map {U' V'} f :=
    TypeCat.ofHom fun a' ↦
      ⟨restrictHom f.unop a'.1,
        mem_sections_restrictHom sX' sY' iX iY a A f.unop a'.1 a'.2⟩
  map_id := sorry
  map_comp := sorry

/-- Evaluating `sectionsPresheaf` at an object of `X'_spaces,étale` recovers the
subtype of compatible local lifts. -/
theorem sectionsPresheaf_obj (sX' : X' ⟶ B) (sY' : Y' ⟶ B) (iX : X ⟶ X')
    (iY : Y ⟶ Y') (a : X ⟶ Y) [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (A : (Modules.pullback a).obj (conormalSheaf iY) ⟶ conormalSheaf iX)
    (U' : spacesEtaleSite X') :
    (sectionsPresheaf sX' sY' iX iY a A).obj (op U') =
      { a' : U'.left ⟶ Y' // a' ∈ sections sX' sY' iX iY a A U' } :=
  sorry

/-- The restriction maps of `sectionsPresheaf` are restriction of morphisms along
the underlying map of spaces-étale objects. -/
theorem sectionsPresheaf_map (sX' : X' ⟶ B) (sY' : Y' ⟶ B) (iX : X ⟶ X')
    (iY : Y ⟶ Y') (a : X ⟶ Y) [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (A : (Modules.pullback a).obj (conormalSheaf iY) ⟶ conormalSheaf iX)
    {U' V' : spacesEtaleSite X'} (f : V' ⟶ U')
    (a' : (sectionsPresheaf sX' sY' iX iY a A).obj (op U')) :
    (sectionsPresheaf sX' sY' iX iY a A).map f.op a' =
      ⟨restrictHom f a'.1, mem_sections_restrictHom sX' sY' iX iY a A f a'.1 a'.2⟩ :=
  sorry

/-- Compatible local lifts of `a` form a sheaf of sets on `X'_spaces,étale`. -/
theorem sectionsPresheaf_isSheaf (sX' : X' ⟶ B) (sY' : Y' ⟶ B) (iX : X ⟶ X')
    (iY : Y ⟶ Y') (a : X ⟶ Y) [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (A : (Modules.pullback a).obj (conormalSheaf iY) ⟶ conormalSheaf iX) :
    Presheaf.IsSheaf (spacesEtaleTopology X') (sectionsPresheaf sX' sY' iX iY a A) :=
  sorry

/-- The sheaf of compatible local deformations of `a` on the spaces-étale site of
`X'`. -/
noncomputable def sectionsSheaf (sX' : X' ⟶ B) (sY' : Y' ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y)
    [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (A : (Modules.pullback a).obj (conormalSheaf iY) ⟶ conormalSheaf iX) :
    Sheaf (spacesEtaleTopology X') (Type (u + 1)) :=
  ⟨sectionsPresheaf sX' sY' iX iY a A, sectionsPresheaf_isSheaf sX' sY' iX iY a A⟩

/-- Evaluating `sectionsSheaf` at an object of `X'_spaces,étale` recovers the
subtype of compatible local lifts. -/
theorem sectionsSheaf_obj (sX' : X' ⟶ B) (sY' : Y' ⟶ B) (iX : X ⟶ X')
    (iY : Y ⟶ Y') (a : X ⟶ Y) [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (A : (Modules.pullback a).obj (conormalSheaf iY) ⟶ conormalSheaf iX)
    (U' : spacesEtaleSite X') :
    (sectionsSheaf sX' sY' iX iY a A).obj.obj (op U') =
      { a' : U'.left ⟶ Y' // a' ∈ sections sX' sY' iX iY a A U' } :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.Deformation
