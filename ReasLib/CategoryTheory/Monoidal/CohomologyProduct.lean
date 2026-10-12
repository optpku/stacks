/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.CommSq
import Mathlib.Tactic.CrossRefAttribute

/-!
# Graded pairings for binary functors

The reusable categorical content of a cohomology product is a family of natural transformations
between two binary functors. This leaf does not assume a monoidal structure, a unit, symmetry, or
any associativity law. Those laws belong to a more structured owner when they are available.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe uι₁ uι₂ uι₃ uC₁ vC₁ uC₂ vC₂ uC₃ vC₃ uE₁ vE₁ uE₂ vE₂ uE₃ vE₃

namespace CategoryTheory

variable {ι₁ : Type uι₁} {ι₂ : Type uι₂} {ι₃ : Type uι₃}
variable {C₁ : Type uC₁} [Category.{vC₁} C₁]
variable {C₂ : Type uC₂} [Category.{vC₂} C₂]
variable {C₃ : Type uC₃} [Category.{vC₃} C₃]
variable {E₁ : Type uE₁} [Category.{vE₁} E₁]
variable {E₂ : Type uE₂} [Category.{vE₂} E₂]
variable {E₃ : Type uE₃} [Category.{vE₃} E₃]

/-- A raw graded pairing between two families of functors.

For `i : ι₁` and `j : ι₂`, `product i j` maps the value of the target binary functor on the two
graded outputs to the output in degree `degree i j` of a third functor family. The binary functors are
explicit data: derived tensor models are generally not definitionally equal, and a derived category
need not carry a chosen monoidal instance.
-/
@[stacks 0G77 "graded pairing for binary functors"]
structure GradedPairing
    (H₁ : ι₁ → C₁ ⥤ E₁) (H₂ : ι₂ → C₂ ⥤ E₂) (H₃ : ι₃ → C₃ ⥤ E₃)
    (degree : ι₁ → ι₂ → ι₃)
    (tensorC : C₁ × C₂ ⥤ C₃) (tensorE : E₁ × E₂ ⥤ E₃) where
  /-- The natural transformation in two fixed degrees. -/
  product : ∀ i j, Functor.prod (H₁ i) (H₂ j) ⋙ tensorE ⟶ tensorC ⋙ H₃ (degree i j)

namespace GradedPairing

variable {H₁ : ι₁ → C₁ ⥤ E₁} {H₂ : ι₂ → C₂ ⥤ E₂} {H₃ : ι₃ → C₃ ⥤ E₃}
variable {degree : ι₁ → ι₂ → ι₃}
variable {tensorC : C₁ × C₂ ⥤ C₃} {tensorE : E₁ × E₂ ⥤ E₃}
variable (P : GradedPairing H₁ H₂ H₃ degree tensorC tensorE)

/-- Evaluate a graded pairing at a pair of objects. -/
@[stacks 0G77 "graded pairing component"]
abbrev app (i : ι₁) (j : ι₂) (K : C₁) (L : C₂) :
    tensorE.obj ((H₁ i).obj K, (H₂ j).obj L) ⟶
      (H₃ (degree i j)).obj (tensorC.obj (K, L)) :=
  (P.product i j).app (K, L)

/-- Postcompose a graded pairing with a morphism out of the source binary operation. -/
@[stacks 0G77 "graded pairing mapped component"]
abbrev map (i : ι₁) (j : ι₂) (K : C₁) (L : C₂) {M : C₃}
    (f : tensorC.obj (K, L) ⟶ M) :
    tensorE.obj ((H₁ i).obj K, (H₂ j).obj L) ⟶ (H₃ (degree i j)).obj M :=
  P.app i j K L ≫ (H₃ (degree i j)).map f

/-- Naturality of a graded pairing in both input variables. -/
@[stacks 0G77 "graded pairing naturality", reassoc (attr := simp)]
theorem naturality (i : ι₁) (j : ι₂) {K K' : C₁} {L L' : C₂}
    (f : K ⟶ K') (g : L ⟶ L') :
    tensorE.map (Prod.mkHom ((H₁ i).map f) ((H₂ j).map g)) ≫ P.app i j K' L' =
      P.app i j K L ≫ (H₃ (degree i j)).map (tensorC.map (Prod.mkHom f g)) := sorry

/-- Naturality transports a commuting square through a graded pairing. -/
@[stacks 0G77 "graded pairing commuting square"]
theorem map_commSq (i : ι₁) (j : ι₂)
    {K K' : C₁} {L L' : C₂} {M M' : C₃}
    (a : K ⟶ K') (b : L ⟶ L')
    (f : tensorC.obj (K, L) ⟶ M) (g : tensorC.obj (K', L') ⟶ M') (c : M ⟶ M')
    (h : CommSq f (tensorC.map (Prod.mkHom a b)) c g) :
    CommSq
      (P.map i j K L f)
      (tensorE.map (Prod.mkHom ((H₁ i).map a) ((H₂ j).map b)))
      ((H₃ (degree i j)).map c)
      (P.map i j K' L' g) := sorry

/-- The specialization of `map_commSq` with the left input fixed and the right input varying. -/
@[stacks 0G77 "graded pairing fixed-left commuting square"]
theorem map_commSq_right (i : ι₁) (j : ι₂)
    {K : C₁} {L L' : C₂} {M M' : C₃}
    (b : L ⟶ L')
    (f : tensorC.obj (K, L) ⟶ M) (g : tensorC.obj (K, L') ⟶ M') (c : M ⟶ M')
    (h : CommSq f (tensorC.map (Prod.mkHom (𝟙 K) b)) c g) :
    CommSq
      (P.map i j K L f)
      (tensorE.map (Prod.mkHom (𝟙 ((H₁ i).obj K)) ((H₂ j).map b)))
      ((H₃ (degree i j)).map c)
      (P.map i j K L' g) := sorry

/-- The specialization of `map_commSq` with the right input fixed and the left input varying. -/
@[stacks 0G77 "graded pairing fixed-right commuting square"]
theorem map_commSq_left (i : ι₁) (j : ι₂)
    {K K' : C₁} {L : C₂} {M M' : C₃}
    (a : K ⟶ K')
    (f : tensorC.obj (K, L) ⟶ M) (g : tensorC.obj (K', L) ⟶ M') (c : M ⟶ M')
    (h : CommSq f (tensorC.map (Prod.mkHom a (𝟙 L))) c g) :
    CommSq
      (P.map i j K L f)
      (tensorE.map (Prod.mkHom ((H₁ i).map a) (𝟙 ((H₂ j).obj L))))
      ((H₃ (degree i j)).map c)
      (P.map i j K' L g) := sorry

end GradedPairing

/-- The self-pairing view for one graded family indexed by an additive type.

Use `GradedPairing` directly when the two inputs have different categories, degree types, or output
family. -/
@[stacks 0G77 "self graded cohomology product view"]
abbrev CohomologyProduct {ι : Type uι₁} [Add ι]
    {C : Type uC₁} [Category.{vC₁} C] {E : Type uE₁} [Category.{vE₁} E]
    (H : ι → C ⥤ E) (tensorC : C × C ⥤ C) (tensorE : E × E ⥤ E) :=
  GradedPairing H H H (fun i j : ι => i + j) tensorC tensorE

namespace CohomologyProduct

variable {ι : Type uι₁} [Add ι]
variable {C : Type uC₁} [Category.{vC₁} C] {E : Type uE₁} [Category.{vE₁} E]
variable {tensorC : C × C ⥤ C} {tensorE : E × E ⥤ E} {H : ι → C ⥤ E}
variable (P : CohomologyProduct H tensorC tensorE)

/-- The component of a self graded product at a pair of objects. -/
abbrev app (i j : ι) (K L : C) := GradedPairing.app P i j K L

/-- Postcompose a self graded product with a morphism out of its source tensor. -/
abbrev map (i j : ι) (K L : C) {M : C} (f : tensorC.obj (K, L) ⟶ M) :=
  GradedPairing.map P i j K L f

/-- Naturality of a self graded product in both tensor factors. -/
@[stacks 0G77 "self graded product naturality", reassoc (attr := simp)]
theorem naturality (i j : ι) {K K' L L' : C} (f : K ⟶ K') (g : L ⟶ L') :
    tensorE.map (Prod.mkHom ((H i).map f) ((H j).map g)) ≫ P.app i j K' L' =
      P.app i j K L ≫ (H (i + j)).map (tensorC.map (Prod.mkHom f g)) := sorry

/-- Transport a commuting square through a self graded product. -/
@[stacks 0G77 "self graded product commuting square"]
theorem map_commSq (i j : ι) {K K' L L' M M' : C}
    (a : K ⟶ K') (b : L ⟶ L')
    (f : tensorC.obj (K, L) ⟶ M) (g : tensorC.obj (K', L') ⟶ M') (c : M ⟶ M')
    (h : CommSq f (tensorC.map (Prod.mkHom a b)) c g) :
    CommSq (P.map i j K L f)
      (tensorE.map (Prod.mkHom ((H i).map a) ((H j).map b)))
      ((H (i + j)).map c) (P.map i j K' L' g) := sorry

/-- The fixed-left specialization of `map_commSq`. -/
@[stacks 0G77 "self graded product fixed-left commuting square"]
theorem map_commSq_right (i j : ι) {K : C} {L L' M M' : C} (b : L ⟶ L')
    (f : tensorC.obj (K, L) ⟶ M) (g : tensorC.obj (K, L') ⟶ M') (c : M ⟶ M')
    (h : CommSq f (tensorC.map (Prod.mkHom (𝟙 K) b)) c g) :
    CommSq (P.map i j K L f)
      (tensorE.map (Prod.mkHom (𝟙 ((H i).obj K)) ((H j).map b)))
      ((H (i + j)).map c) (P.map i j K L' g) := sorry

/-- The fixed-right specialization of `map_commSq`. -/
@[stacks 0G77 "self graded product fixed-right commuting square"]
theorem map_commSq_left (i j : ι) {K K' L M M' : C} (a : K ⟶ K')
    (f : tensorC.obj (K, L) ⟶ M) (g : tensorC.obj (K', L) ⟶ M') (c : M ⟶ M')
    (h : CommSq f (tensorC.map (Prod.mkHom a (𝟙 L))) c g) :
    CommSq (P.map i j K L f)
      (tensorE.map (Prod.mkHom ((H i).map a) (𝟙 ((H j).obj L))))
      ((H (i + j)).map c) (P.map i j K' L g) := sorry

end CohomologyProduct

end CategoryTheory
