module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Pullback
public import ReasLib.AlgebraicTopology.Cech.Nerve.LowDegree
public import stacks_project.Chap85.Definition_85_27_1_Cartesian
public import stacks_project.Chap85.Definition_85_27_3_Nerve
public import stacks_project.Chap85.Lemma_85_29_1_Nerve

/-!
# Target simplicial morphism of a groupoid scheme

A groupoid scheme `G` over `S` determines a morphism `t_•` from the Čech nerve of `s` to the
associated simplicial scheme, sending `(r₀, …, rₙ)` to `(r₀ ∘ r₁⁻¹, …, rₙ₋₁ ∘ rₙ⁻¹)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}} (G : GroupoidScheme S)

/-- The later arrow and the inverse of the earlier arrow of a common-source pair are composable. -/
theorem rightDivisionCondition :
    pullback.fst G.s G.s ≫ G.s = (pullback.snd G.s G.s ≫ G.i) ≫ G.t :=
  sorry

/-- For two arrows with a common source, compose the first with the inverse of the second. -/
def rightDivision : pullback G.s G.s ⟶ G.R :=
  G.compose (pullback.fst G.s G.s) (pullback.snd G.s G.s ≫ G.i) (rightDivisionCondition G)

/-- The source of a right quotient is the target of the second arrow. -/
theorem rightDivision_source : G.rightDivision ≫ G.s = pullback.snd G.s G.s ≫ G.t :=
  sorry

/-- The target of a right quotient is the target of the first arrow. -/
theorem rightDivision_target : G.rightDivision ≫ G.t = pullback.fst G.s G.s ≫ G.t :=
  sorry

/-- Degree `n` of the Čech nerve of `s`, as a scheme over `S` via the base projection through `U`. -/
def sourceCechOver (n : SimplexCategoryᵒᵖ) : Over S :=
  Over.mk (Arrow.cechNerve.base (Arrow.mk G.s.left) n ≫ G.U.hom)

/-- The structure morphism of `sourceCechOver` is the Čech-nerve base projection followed by `U ⟶ S`. -/
theorem sourceCechOver_hom (n : SimplexCategoryᵒᵖ) :
    (sourceCechOver G n).hom = Arrow.cechNerve.base (Arrow.mk G.s.left) n ≫ G.U.hom :=
  sorry

/-- Each Čech-nerve vertex projection of `s` is a morphism over `S`. -/
theorem sourceCechπOver_w (n : SimplexCategoryᵒᵖ) (i : Fin (n.unop.len + 1)) :
    Arrow.cechNerve.π (Arrow.mk G.s.left) n i ≫ G.R.hom = (sourceCechOver G n).hom :=
  sorry

/-- The vertex projection `π i : (R/U)_n ⟶ R` as a morphism of schemes over `S`. -/
def sourceCechπOver (n : SimplexCategoryᵒᵖ) (i : Fin (n.unop.len + 1)) :
    sourceCechOver G n ⟶ G.R :=
  Over.homMk (Arrow.cechNerve.π (Arrow.mk G.s.left) n i) (sourceCechπOver_w G n i)

/-- The underlying scheme morphism of `sourceCechπOver` is the Čech-nerve vertex projection. -/
theorem sourceCechπOver_left (n : SimplexCategoryᵒᵖ) (i : Fin (n.unop.len + 1)) :
    (sourceCechπOver G n i).left = Arrow.cechNerve.π (Arrow.mk G.s.left) n i :=
  sorry

/-- Consecutive Čech projections become composable after inverting the later one. -/
theorem sourceCechRightDivisionCondition (n : SimplexCategoryᵒᵖ) (i : Fin n.unop.len) :
    sourceCechπOver G n i.castSucc ≫ G.s =
      (sourceCechπOver G n i.succ ≫ G.i) ≫ G.t :=
  sorry

/-- The source formula component `rᵢ ∘ rᵢ₊₁⁻¹` on a Čech degree. -/
def sourceCechRightDivision (n : SimplexCategoryᵒᵖ) (i : Fin n.unop.len) :
    sourceCechOver G n ⟶ G.R :=
  G.compose (sourceCechπOver G n i.castSucc) (sourceCechπOver G n i.succ ≫ G.i)
    (sourceCechRightDivisionCondition G n i)

/-- The source of `rᵢ ∘ rᵢ₊₁⁻¹` is the target of `rᵢ₊₁`. -/
theorem sourceCechRightDivision_source (n : SimplexCategoryᵒᵖ) (i : Fin n.unop.len) :
    sourceCechRightDivision G n i ≫ G.s = sourceCechπOver G n i.succ ≫ G.t :=
  sorry

/-- The target of `rᵢ ∘ rᵢ₊₁⁻¹` is the target of `rᵢ`. -/
theorem sourceCechRightDivision_target (n : SimplexCategoryᵒᵖ) (i : Fin n.unop.len) :
    sourceCechRightDivision G n i ≫ G.t = sourceCechπOver G n i.castSucc ≫ G.t :=
  sorry

/-- The zeroth face of the Čech nerve of `s` is a morphism over `S`. -/
theorem sourceCechFaceZero_w (n : ℕ) :
    (Scheme.Hom.simplicialScheme G.s.left).δ (0 : Fin (n + 3)) ≫
        (sourceCechOver G (op ⦋n + 1⦌)).hom =
      (sourceCechOver G (op ⦋n + 2⦌)).hom :=
  sorry

/-- The zeroth face `(R/U)_{n+2} ⟶ (R/U)_{n+1}`, as a morphism of schemes over `S`. -/
def sourceCechFaceZero (n : ℕ) :
    sourceCechOver G (op ⦋n + 2⦌) ⟶ sourceCechOver G (op ⦋n + 1⦌) :=
  Over.homMk ((Scheme.Hom.simplicialScheme G.s.left).δ (0 : Fin (n + 3)))
    (sourceCechFaceZero_w G n)

/-- The underlying scheme morphism of `sourceCechFaceZero` is the zeroth Čech face. -/
theorem sourceCechFaceZero_left (n : ℕ) :
    (sourceCechFaceZero G n).left =
      (Scheme.Hom.simplicialScheme G.s.left).δ (0 : Fin (n + 3)) :=
  sorry

/-- The later-most right division and a remaining `targetOver` factor are compatible over
`(s, t)` in the recursive fibre product. -/
theorem targetOverLift_w (n : ℕ)
    (rest : sourceCechOver G (op ⦋n + 1⦌) ⟶ composable G (n + 1)) :
    sourceCechRightDivision G (op ⦋n + 2⦌) 0 ≫ G.s =
      (sourceCechFaceZero G n ≫ rest) ≫
        composableπ G (n + 1) ⟨0, Nat.succ_pos n⟩ ≫ G.t :=
  sorry

/-- The degree-`n` component of `t_•`, as a morphism over `S` into the n-fold fibre product of `R`. -/
def targetOver : (n : ℕ) → (sourceCechOver G (op ⦋n⦌) ⟶ composable G n)
  | 0 => sourceCechπOver G (op ⦋0⦌) 0 ≫ G.t
  | 1 => sourceCechRightDivision G (op ⦋1⦌) 0
  | n + 2 =>
      pullback.lift (sourceCechRightDivision G (op ⦋n + 2⦌) 0)
        (sourceCechFaceZero G n ≫ targetOver (n + 1))
        (targetOverLift_w G n (targetOver (n + 1)))

/-- The later-most right division and the remaining `targetOver` factors are compatible over
`(s, t)` in the recursive fibre product. -/
theorem targetOver_succ_w (n : ℕ) :
    sourceCechRightDivision G (op ⦋n + 2⦌) 0 ≫ G.s =
      (sourceCechFaceZero G n ≫ targetOver G (n + 1)) ≫
        composableπ G (n + 1) ⟨0, Nat.succ_pos n⟩ ≫ G.t :=
  sorry

/-- In degree `0`, `targetOver` is the target map after the unique Čech projection. -/
theorem targetOver_zero : targetOver G 0 = sourceCechπOver G (op ⦋0⦌) 0 ≫ G.t :=
  sorry

/-- In degree `1`, `targetOver` is right division of the two Čech projections. -/
theorem targetOver_one : targetOver G 1 = sourceCechRightDivision G (op ⦋1⦌) 0 :=
  sorry

/-- The later-first projections of `targetOver` are the consecutive right divisions of Čech
projections. -/
theorem targetSimplicial_π (n : ℕ) (i : Fin n) :
    targetOver G n ≫ composableπ G n i = sourceCechRightDivision G (op ⦋n⦌) i :=
  sorry

/-- Simplex operators intertwine the scheme-level components of `t_•`. -/
theorem targetSimplicial_naturality :
    ∀ ⦃n m : SimplexCategoryᵒᵖ⦄ (f : n ⟶ m),
      (Scheme.Hom.simplicialScheme G.s.left).map f ≫
          (targetOver G m.unop.len).left ≫ composableComparison G m.unop.len =
        ((targetOver G n.unop.len).left ≫ composableComparison G n.unop.len) ≫
          (simplicialScheme G).map f :=
  sorry

/-- The cartesian morphism `t_• : (R/U)_• ⟶ X` associated to a groupoid scheme. -/
def targetSimplicial : Scheme.Hom.simplicialScheme G.s.left ⟶ simplicialScheme G where
  app n := (targetOver G n.unop.len).left ≫ composableComparison G n.unop.len
  naturality := targetSimplicial_naturality G

/-- After identifying degree `0` of `(R/U)_•` with `R` and degree `0` of `X` with `U`, the
component of `t_•` is the target map `t`. -/
theorem targetSimplicial_app_zero :
    (Arrow.cechNerve.degreeZero.iso (Arrow.mk G.s.left)).inv ≫
        (targetSimplicial G).app (op ⦋0⦌) ≫ (degreeZero.iso G).hom =
      G.t.left :=
  sorry

/-- After identifying degree `1` of `(R/U)_•` with `pullback s s` and degree `1` of `X` with `R`,
the component of `t_•` is right division `(r₀, r₁) ↦ r₀ ∘ r₁⁻¹`. -/
theorem targetSimplicial_app_one :
    (Arrow.cechNerve.degreeOne.pullbackIso (Arrow.mk G.s.left)).inv ≫
        (targetSimplicial G).app (op ⦋1⦌) ≫ (degreeOne.iso G).hom =
      (PreservesPullback.iso (Over.forget S) G.s G.s).inv ≫ G.rightDivision.left :=
  sorry

/-- After identifying degree `2` of `X` with `R ×_{s,U,t} R`, the first factor of `t_•` is
`r₀ ∘ r₁⁻¹`. -/
theorem targetSimplicial_app_two_fst :
    (targetSimplicial G).app (op ⦋2⦌) ≫ (degreeTwo.iso G).hom ≫ (pullback.fst G.s G.t).left =
      (sourceCechRightDivision G (op ⦋2⦌) 0).left :=
  sorry

/-- After identifying degree `2` of `X` with `R ×_{s,U,t} R`, the second factor of `t_•` is
`r₁ ∘ r₂⁻¹`. -/
theorem targetSimplicial_app_two_snd :
    (targetSimplicial G).app (op ⦋2⦌) ≫ (degreeTwo.iso G).hom ≫ (pullback.snd G.s G.t).left =
      (sourceCechRightDivision G (op ⦋2⦌) 1).left :=
  sorry

namespace targetSimplicial

/-- The morphism `t_•` is cartesian: every simplex-operator naturality square is a fibre square. -/
instance instIsCartesian : SimplicialObject.IsCartesian (targetSimplicial G) := sorry

end targetSimplicial

end AlgebraicGeometry.GroupoidScheme

