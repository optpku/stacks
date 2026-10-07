module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Products.Basic
public import stacks_project.Chap92.Lemma_92_4_1_PolynomialOver
import Mathlib.Tactic.CrossRefAttribute

/-!
# Underived lower shriek on a polynomial algebra

Lemma 92.4.6 records that if `B` is a polynomial `A`-algebra, then the underived
lower shriek `π_!` of `π` from 92.4.0.1 is exact and evaluates a presheaf at the
identity object `B ⟶ B`. The source proof applies Lemma 92.4.1 to the constant
simplicial algebra on `B`; equivalently, `B ⟶ B` is terminal in `PolynomialOver`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u v w

namespace Algebra.PolynomialOver

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [IsPolynomial A B]

/-- The identity object `B ⟶ B` in the category of polynomial `A`-algebra maps to `B`. -/
def idObj : PolynomialOver A B where
  obj := Over.mk (𝟙 (CommAlgCat.of A B))
  property := (inferInstance : IsPolynomial A B)

/-- The underlying over-object of `idObj` is the identity morphism of `CommAlgCat.of A B`. -/
theorem idObj_obj : (idObj A B).obj = Over.mk (𝟙 (CommAlgCat.of A B)) :=
  sorry

/-- The unique morphism from an object `X` of `PolynomialOver A B` to the identity object,
given by the structure map of `X`. -/
def idHom {X : PolynomialOver A B} : X ⟶ idObj A B :=
  ObjectProperty.homMk (Over.homMk X.obj.hom (Category.comp_id X.obj.hom))

/-- The underlying `A`-algebra map of `idHom` is the structure morphism of `X`. -/
theorem idHom_left (X : PolynomialOver A B) :
    (idHom A B : X ⟶ idObj A B).hom.left = X.obj.hom :=
  sorry

/-- The identity object `B ⟶ B` is terminal in `PolynomialOver A B`. -/
def idObj_isTerminal : IsTerminal (idObj A B) :=
  IsTerminal.ofUniqueHom (fun X ↦ idHom A B) (fun _ _ ↦ sorry)

/-- Maps into the identity object of `PolynomialOver A B` are unique. -/
theorem idObj_isTerminal_unique {X : PolynomialOver A B} (f : X ⟶ idObj A B) :
    f = (idObj_isTerminal A B).from X :=
  sorry

end Algebra.PolynomialOver

namespace Algebra.PolynomialSite

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [IsPolynomial A B]

/-- The identity object `B ⟶ B` as an object of the opposite polynomial site `C_{B/A}`. -/
def idObj : PolynomialSite A B :=
  op (PolynomialOver.idObj A B)

/-- Forgetting the opposite recovers the identity object of `PolynomialOver A B`. -/
theorem idObj_unop : (idObj A B).unop = PolynomialOver.idObj A B :=
  sorry

/-- The identity object `B ⟶ B` as an object of `(PolynomialSite A B)ᵒᵖ`, the indexing
category of underived `π_!`. -/
def evalObj : (PolynomialSite A B)ᵒᵖ :=
  op (idObj A B)

/-- Forgetting the opposite recovers the identity object of `PolynomialSite A B`. -/
theorem evalObj_unop : (evalObj A B).unop = idObj A B :=
  sorry

/-- The identity object is terminal in `(PolynomialSite A B)ᵒᵖ`. -/
def evalObj_isTerminal : IsTerminal (evalObj A B) :=
  terminalOpOfInitial (initialOpOfTerminal (PolynomialOver.idObj_isTerminal A B))

/-- Maps into the identity object of `(PolynomialSite A B)ᵒᵖ` are unique. -/
theorem evalObj_isTerminal_unique {X : (PolynomialSite A B)ᵒᵖ} (f : X ⟶ evalObj A B) :
    f = (evalObj_isTerminal A B).from X :=
  sorry

variable (𝒜 : Type v) [Category.{w} 𝒜] [Abelian 𝒜]
  [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ 𝒜]

/-- Lemma 92.4.6 (1). If `B` is a polynomial algebra over the ring `A`, then with `π` as in
92.4.0.1 we have that `π_!` is exact, recorded as exactness of `colim` on
`(PolynomialSite A B)ᵒᵖ`-valued presheaves. -/
@[stacks 08QG]
theorem lowerShriek_exact :
    exactFunctor ((PolynomialSite A B)ᵒᵖ ⥤ 𝒜) 𝒜
      (colim : ((PolynomialSite A B)ᵒᵖ ⥤ 𝒜) ⥤ 𝒜) :=
  sorry

/-- Lemma 92.4.6 (2). If `B` is a polynomial algebra over the ring `A`, then with `π` as in
92.4.0.1 we have `π_! F ≅ F(B ⟶ B)`, as the functor isomorphism of underived `π_!`
(`colim`) with evaluation at the identity object. -/
@[stacks 08QG]
def lowerShriekIsoEval :
    (colim : ((PolynomialSite A B)ᵒᵖ ⥤ 𝒜) ⥤ 𝒜) ≅
      (evaluation ((PolynomialSite A B)ᵒᵖ) 𝒜).obj (evalObj A B) :=
  NatIso.ofComponents
    (fun F ↦ (colimit.isColimit F).coconePointUniqueUpToIso
      (colimitOfDiagramTerminal (evalObj_isTerminal A B) F))
    (fun {_ _} _ ↦ sorry)

/-- Objectwise form of the identification `π_! F ≅ F(B ⟶ B)`. -/
theorem lowerShriekIsoEval_app (F : (PolynomialSite A B)ᵒᵖ ⥤ 𝒜) :
    (lowerShriekIsoEval A B 𝒜).app F =
      (colimit.isColimit F).coconePointUniqueUpToIso
        (colimitOfDiagramTerminal (evalObj_isTerminal A B) F) :=
  sorry

end Algebra.PolynomialSite
