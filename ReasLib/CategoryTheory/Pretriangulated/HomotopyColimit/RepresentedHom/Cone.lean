/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Presentation.Definition
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.RepresentedHom.Tower
public import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Tactic.CrossRefAttribute

/-!
# The represented Hom cone of a homotopy-colimit presentation

@stack 0CQX

A telescope presentation determines a cone from `Hom_D(X, L)` to the inverse system
`n ↦ Hom_D(K_n, L)`. This leaf owns that cone and its canonical map to the inverse limit.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

noncomputable section

universe u v

namespace CategoryTheory.HomotopyColimit.RepresentedHom

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-- Precomposition with the `n`th leg of a telescope presentation, regarded as a morphism of
represented Hom groups. -/
@[stacks 0CQX]
def homConeApp {K : ℕ ⥤ D} {X : D} (P : Presentation K X) (L : D) (n : ℕ) :
    (preadditiveYoneda.obj L).obj (op X) ⟶ (tower K L).obj (op n) :=
  (preadditiveYoneda.obj L).map (P.ι n).op

/-- The stage map of the represented Hom cone sends `f : X ⟶ L` to `P.ι n ≫ f`. -/
@[simp]
theorem homConeApp_apply {K : ℕ ⥤ D} {X : D} (P : Presentation K X) (L : D)
    (n : ℕ) (f : X ⟶ L) :
    homConeApp P L n f = P.ι n ≫ f := sorry

/-- The stage maps of the represented Hom cone commute with every transition of the
represented Hom tower. -/
@[reassoc, stacks 0CQX]
theorem homConeApp_transition {K : ℕ ⥤ D} {X : D} (P : Presentation K X)
    (L : D) {i j : ℕ} (hij : i ≤ j) :
    homConeApp P L j ≫ (tower K L).transitionMap hij = homConeApp P L i := sorry

/-- The successor specialization of compatibility for the represented Hom cone. -/
@[reassoc, stacks 0CQX]
theorem homConeApp_transition_succ {K : ℕ ⥤ D} {X : D} (P : Presentation K X)
    (L : D) (n : ℕ) :
    homConeApp P L (n + 1) ≫ (tower K L).transitionMap (Nat.le_succ n) =
      homConeApp P L n := sorry

/-- The successor equation for `homConeApp` in the form required by
`NatTrans.ofOpSequence`. -/
theorem homConeApp_sequence {K : ℕ ⥤ D} {X : D} (P : Presentation K X)
    (L : D) (n : ℕ) :
    ((Functor.const ℕᵒᵖ).obj ((preadditiveYoneda.obj L).obj (op X))).map
          (homOfLE (Nat.le_succ n)).op ≫ homConeApp P L n =
      homConeApp P L (n + 1) ≫ (tower K L).map (homOfLE (Nat.le_succ n)).op := sorry

/-- The natural transformation from the constant represented Hom group to the represented Hom
tower determined by a telescope presentation. -/
@[stacks 0CQX]
def homConeNatTrans {K : ℕ ⥤ D} {X : D} (P : Presentation K X) (L : D) :
    (Functor.const ℕᵒᵖ).obj ((preadditiveYoneda.obj L).obj (op X)) ⟶ tower K L :=
  NatTrans.ofOpSequence (homConeApp P L) (homConeApp_sequence P L)

/-- The component of the represented Hom cone transformation is precomposition with the
corresponding presentation leg. -/
@[simp]
theorem homConeNatTrans_app {K : ℕ ⥤ D} {X : D} (P : Presentation K X)
    (L : D) (n : ℕ) :
    (homConeNatTrans P L).app (op n) = homConeApp P L n := sorry

/-- The cone from `Hom_D(X, L)` to the represented Hom tower induced by a telescope
presentation of `X`. -/
@[stacks 0CQX]
def homCone {K : ℕ ⥤ D} {X : D} (P : Presentation K X) (L : D) :
    Cone (tower K L) where
  pt := (preadditiveYoneda.obj L).obj (op X)
  π := homConeNatTrans P L

/-- The `n`th projection of `homCone` is precomposition with `P.ι n`. -/
@[simp]
theorem homCone_π_app {K : ℕ ⥤ D} {X : D} (P : Presentation K X)
    (L : D) (n : ℕ) :
    (homCone P L).π.app (op n) = homConeApp P L n := sorry

/-- The canonical morphism from `Hom_D(X, L)` to the inverse limit of the represented Hom
tower associated to a telescope presentation of `X`. -/
@[stacks 0CQX]
def homToLimit {K : ℕ ⥤ D} {X : D} (P : Presentation K X) (L : D) :
    (preadditiveYoneda.obj L).obj (op X) ⟶ limit (tower K L) :=
  limit.lift (tower K L) (homCone P L)

/-- Projecting `homToLimit` to stage `n` gives precomposition with the `n`th presentation
leg. -/
@[reassoc (attr := simp), stacks 0CQX]
theorem homToLimit_comp_π {K : ℕ ⥤ D} {X : D} (P : Presentation K X)
    (L : D) (n : ℕ) :
    homToLimit P L ≫ limit.π (tower K L) (op n) = homConeApp P L n := sorry

/-- Elementwise, the `n`th projection of `homToLimit` sends `f` to `P.ι n ≫ f`. -/
@[simp]
theorem homToLimit_π_apply {K : ℕ ⥤ D} {X : D} (P : Presentation K X)
    (L : D) (n : ℕ) (f : X ⟶ L) :
    (limit.π (tower K L) (op n)) (homToLimit P L f) = P.ι n ≫ f := sorry

end CategoryTheory.HomotopyColimit.RepresentedHom

end
