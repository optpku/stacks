/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicTopology.SimplexCategory.Rev
public import Mathlib.AlgebraicTopology.SimplicialObject.Coskeletal
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import ReasLib.AlgebraicGeometry.GroupoidScheme
public import ReasLib.AlgebraicTopology.SimplexCategory.Truncated.KanExtension.FiniteInstances
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Coskeleton.Degreewise

/-!
# Internal nerve of a groupoid scheme

A groupoid scheme `(U, R, s, t, c, e, i)` over `S` determines a 2-truncated simplicial object
in `Over S` with terms `U`, `R`, and `pullback s t`, and the associated simplicial scheme is the
2-coskeleton of that truncation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows Opposite
open scoped Simplicial SimplexCategory.Truncated

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- Auxiliary recursive data for the n-fold fibre product of `R` over `(s, t)`, together with the
later-first projections onto `R`. -/
def composableWithπ {S : Scheme.{u}} (G : GroupoidScheme S) :
    (n : ℕ) → Σ' (X : Over S), Fin n → (X ⟶ G.R)
  | 0 => ⟨G.U, fun i => nomatch i⟩
  | 1 => ⟨G.R, fun _ => 𝟙 G.R⟩
  | n + 2 =>
      let prev := composableWithπ G (n + 1)
      let rest := prev.2 ⟨0, Nat.succ_pos n⟩ ≫ G.t
      ⟨pullback G.s rest, fun i =>
        if h : i.1 = 0 then pullback.fst G.s rest
        else pullback.snd G.s rest ≫ prev.2 (Fin.subNat 1 i (Nat.pos_of_ne_zero h))⟩

/-- The n-fold fibre product `R ×_{s,U,t} ⋯ ×_{s,U,t} R` with `n` factors, as an object over `S`.
The `0`-fold product is `U` and the `1`-fold product is `R`. -/
def composable {S : Scheme.{u}} (G : GroupoidScheme S) (n : ℕ) : Over S :=
  (composableWithπ G n).1

/-- The later-first family of projections from the n-fold fibre product onto `R`. Index `0` is the
later-most factor. -/
def composableπ {S : Scheme.{u}} (G : GroupoidScheme S) (n : ℕ) :
    Fin n → (composable G n ⟶ G.R) :=
  (composableWithπ G n).2

/-- Notation-friendly alias for `composableπ`. -/
abbrev composable.π {S : Scheme.{u}} (G : GroupoidScheme S) (n : ℕ) :
    Fin n → (composable G n ⟶ G.R) :=
  composableπ G n

/-- The later-most factor projection `X_{n+1} ⟶ R`. -/
def composable.firstArrow {S : Scheme.{u}} (G : GroupoidScheme S) (n : ℕ) :
    composable G (n + 1) ⟶ G.R :=
  composableπ G (n + 1) ⟨0, Nat.succ_pos n⟩

/-- Adjacent later-first projections of the n-fold fibre product are composable over `(s, t)`. -/
theorem composableπ_adjacent {S : Scheme.{u}} (G : GroupoidScheme S) (n : ℕ) (i : Fin n) :
    composableπ G (n + 1) i.castSucc ≫ G.s =
      composableπ G (n + 1) i.succ ≫ G.t :=
  sorry

/-- The vertices of the n-simplex of composable arrows, numbered from source to target. -/
def composable.vertex {S : Scheme.{u}} (G : GroupoidScheme S) (n : ℕ) (i : Fin (n + 1)) :
    composable G n ⟶ G.U :=
  match n, i with
  | 0, _ => 𝟙 G.U
  | n + 1, i =>
      if (i : ℕ) = n + 1 then
        composableπ G (n + 1) ⟨0, Nat.succ_pos n⟩ ≫ G.t
      else
        composableπ G (n + 1) ⟨n - (i : ℕ), Nat.lt_succ_of_le (Nat.sub_le n i)⟩ ≫ G.s

/-- Reconstruct a morphism into the n-fold fibre product from an n-simplex of the point groupoid. -/
def ofComposableArrows {S : Scheme.{u}} (G : GroupoidScheme S) {T : Over S} :
    ∀ n, ComposableArrows (G.groupoidPoints T) n → (T ⟶ composable G n)
  | 0, F => F.obj' 0
  | 1, F => (F.map' 0 1).arrow
  | n + 2, F =>
      pullback.lift (F.map' (n + 1) (n + 2)).arrow
        (ofComposableArrows G (n + 1) F.δlast) sorry

/-- Send a morphism into the n-fold fibre product to an n-simplex of the point groupoid. -/
def toComposableArrows {S : Scheme.{u}} (G : GroupoidScheme S) {T : Over S} :
    ∀ n, (T ⟶ composable G n) → ComposableArrows (G.groupoidPoints T) n
  | 0, p => mk₀ p
  | 1, p => mk₁ (PointHom.ofArrow p rfl rfl)
  | n + 2, p =>
      mkOfObjOfMapSucc (fun i => p ≫ composable.vertex G (n + 2) i) fun i =>
        PointHom.ofArrow
          (p ≫ composableπ G (n + 2) ⟨n + 1 - (i : ℕ), Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)
          sorry sorry

/-- Morphisms into the n-fold fibre product are n-simplices of the point groupoid. -/
def composablePointsEquiv {S : Scheme.{u}} (G : GroupoidScheme S) (n : ℕ) (T : Over S) :
    (T ⟶ composable G n) ≃ ComposableArrows (G.groupoidPoints T) n where
  toFun := toComposableArrows G n
  invFun := ofComposableArrows G n
  left_inv := sorry
  right_inv := sorry

/-- The simplicial operator on n-fold fibre products induced by a morphism of simplices, using the
Stacks face orientation (`d^1_0 = s`) via `SimplexCategory.rev`. -/
def simplexMap {S : Scheme.{u}} (G : GroupoidScheme S) {a b : SimplexCategory} (f : a ⟶ b) :
    composable G b.len ⟶ composable G a.len :=
  ofComposableArrows G a.len
    ((nerve (G.groupoidPoints (composable G b.len))).map (op (SimplexCategory.rev.map f))
      (toComposableArrows G b.len (𝟙 (composable G b.len))))

/-- The 2-truncated simplicial object over `S` with terms `U`, `R`, and `R ×_{s,U,t} R`. -/
def truncatedNerve {S : Scheme.{u}} (G : GroupoidScheme S) :
    SimplicialObject.Truncated (Over S) 2 where
  obj n := composable G n.unop.obj.len
  map f := simplexMap G f.unop.hom
  map_id := sorry
  map_comp := sorry

/-- The simplicial scheme associated to a groupoid scheme, as the 2-coskeleton of
`truncatedNerve`. -/
def simplicialScheme {S : Scheme.{u}} (G : GroupoidScheme S) : SimplicialObject Scheme.{u} :=
  (SimplicialObject.Truncated.cosk 2).obj (truncatedNerve G) ⋙ Over.forget S

/-- Identity-at-target degeneracy `(e ∘ t, 1) : R ⟶ R ×_{s,U,t} R`. -/
def degeneracy_one_zero {S : Scheme.{u}} (G : GroupoidScheme S) : G.R ⟶ pullback G.s G.t :=
  pullback.lift (G.t ≫ G.e) (𝟙 G.R) sorry

/-- Identity-at-source degeneracy `(1, e ∘ s) : R ⟶ R ×_{s,U,t} R`. The source text writes
`(1, e ∘ t)`, which does not land in the fibre product; the groupoid identity axiom forces
`(1, e ∘ s)`. -/
def degeneracy_one_one {S : Scheme.{u}} (G : GroupoidScheme S) : G.R ⟶ pullback G.s G.t :=
  pullback.lift (𝟙 G.R) (G.s ≫ G.e) sorry

/-- The canonical isomorphism between a low-degree value of the 2-coskeleton and the original
truncated term. -/
def degreewiseCounitIso {S : Scheme.{u}} (G : GroupoidScheme S) {k : ℕ} (hk : k ≤ 2) :
    ((SimplicialObject.Truncated.cosk 2).obj (truncatedNerve G)).obj (op ⦋k⦌) ≅
      (truncatedNerve G).obj (op ⦋k, hk⦌₂) :=
  (SimplicialObject.Truncated.coskeleton.degree.isoLimit (truncatedNerve G) ⦋k⦌).trans
    (SimplicialObject.Truncated.coskeleton.degree.inRange.iso (truncatedNerve G) hk)

namespace degreeZero

/-- Degree `0` of the associated simplicial scheme is the object scheme `U`. -/
def iso {S : Scheme.{u}} (G : GroupoidScheme S) :
    simplicialScheme G _⦋0⦌ ≅ G.U.left :=
  (Over.forget S).mapIso (degreewiseCounitIso G (Nat.zero_le 2))

/-- The forward map of `degreeZero.iso` is forgetting the in-range 2-coskeleton coordinate. -/
theorem iso_hom {S : Scheme.{u}} (G : GroupoidScheme S) :
    (iso G).hom = (Over.forget S).map (degreewiseCounitIso G (Nat.zero_le 2)).hom :=
  sorry

/-- The inverse map of `degreeZero.iso` is forgetting the inverse in-range coordinate. -/
theorem iso_inv {S : Scheme.{u}} (G : GroupoidScheme S) :
    (iso G).inv = (Over.forget S).map (degreewiseCounitIso G (Nat.zero_le 2)).inv :=
  sorry

end degreeZero

namespace degreeOne

/-- Degree `1` of the associated simplicial scheme is the arrow scheme `R`. -/
def iso {S : Scheme.{u}} (G : GroupoidScheme S) :
    simplicialScheme G _⦋1⦌ ≅ G.R.left :=
  (Over.forget S).mapIso (degreewiseCounitIso G (by decide : 1 ≤ 2))

/-- The forward map of `degreeOne.iso` is forgetting the in-range 2-coskeleton coordinate. -/
theorem iso_hom {S : Scheme.{u}} (G : GroupoidScheme S) :
    (iso G).hom = (Over.forget S).map (degreewiseCounitIso G (by decide : 1 ≤ 2)).hom :=
  sorry

/-- The inverse map of `degreeOne.iso` is forgetting the inverse in-range coordinate. -/
theorem iso_inv {S : Scheme.{u}} (G : GroupoidScheme S) :
    (iso G).inv = (Over.forget S).map (degreewiseCounitIso G (by decide : 1 ≤ 2)).inv :=
  sorry

end degreeOne

namespace degreeTwo

/-- Degree `2` of the associated simplicial scheme is the fibre product `R ×_{s,U,t} R`. -/
def iso {S : Scheme.{u}} (G : GroupoidScheme S) :
    simplicialScheme G _⦋2⦌ ≅ (pullback G.s G.t).left :=
  (Over.forget S).mapIso (degreewiseCounitIso G (le_rfl : 2 ≤ 2))

/-- The forward map of `degreeTwo.iso` is forgetting the in-range 2-coskeleton coordinate. -/
theorem iso_hom {S : Scheme.{u}} (G : GroupoidScheme S) :
    (iso G).hom = (Over.forget S).map (degreewiseCounitIso G (le_rfl : 2 ≤ 2)).hom :=
  sorry

/-- The inverse map of `degreeTwo.iso` is forgetting the inverse in-range coordinate. -/
theorem iso_inv {S : Scheme.{u}} (G : GroupoidScheme S) :
    (iso G).inv = (Over.forget S).map (degreewiseCounitIso G (le_rfl : 2 ≤ 2)).inv :=
  sorry

end degreeTwo

/-- The matching-diagram value of a structured arrow, as a map out of the n-fold fibre product. -/
def composableMatchingMap {S : Scheme.{u}} (G : GroupoidScheme S) (n : ℕ)
    (g : SimplicialObject.Truncated.coskeleton.degree.Index 2 ⦋n⦌) :
    composable G n ⟶ (truncatedNerve G).obj g.right :=
  simplexMap G g.hom.unop

/-- The matching cone presenting the n-fold fibre product as a cone over the 2-coskeleton
diagram at `⦋n⦌`. -/
def composableMatchingCone {S : Scheme.{u}} (G : GroupoidScheme S) (n : ℕ) :
    Cone (SimplicialObject.Truncated.coskeleton.degree.diagram (truncatedNerve G) ⦋n⦌) where
  pt := composable G n
  π :=
    { app := fun g => composableMatchingMap G n g
      naturality := fun _ _ _ => sorry }

/-- Comparison in `Over S` from the explicit n-fold fibre product to the 2-coskeleton. -/
def composableComparisonOver {S : Scheme.{u}} (G : GroupoidScheme S) (n : ℕ) :
    composable G n ⟶
      ((SimplicialObject.Truncated.cosk 2).obj (truncatedNerve G)).obj (op ⦋n⦌) :=
  limit.lift _ (composableMatchingCone G n) ≫
    (SimplicialObject.Truncated.coskeleton.degree.isoLimit (truncatedNerve G) ⦋n⦌).inv

/-- Canonical comparison from the n-fold fibre product of `R` over `(s, t)` to degree `n` of the
associated simplicial scheme. -/
def composableComparison {S : Scheme.{u}} (G : GroupoidScheme S) (n : ℕ) :
    (composable G n).left ⟶ simplicialScheme G _⦋n⦌ :=
  (composableComparisonOver G n).left

/-- The comparison identifying `X_n` with the n-fold fibre product is an isomorphism. -/
theorem composableComparison_isIso {S : Scheme.{u}} (G : GroupoidScheme S) (n : ℕ) :
    IsIso (composableComparison G n) :=
  sorry

/-- Face operators on n-fold fibre products, with Stacks numbering `d^n_i`. -/
def composable.face {S : Scheme.{u}} (G : GroupoidScheme S) (n : ℕ) (i : Fin (n + 2)) :
    composable G (n + 1) ⟶ composable G n :=
  simplexMap G (SimplexCategory.δ i)

/-- Degeneracy operators on n-fold fibre products. -/
def composable.degeneracy {S : Scheme.{u}} (G : GroupoidScheme S) (n : ℕ) (i : Fin (n + 1)) :
    composable G n ⟶ composable G (n + 1) :=
  simplexMap G (SimplexCategory.σ i)

/-- Face operators on n-fold fibre products are compatible with the comparison to the associated
simplicial scheme. -/
theorem composableComparison_face {S : Scheme.{u}} (G : GroupoidScheme S)
    (n : ℕ) (i : Fin (n + 2)) :
    (composable.face G n i).left ≫ composableComparison G n =
      composableComparison G (n + 1) ≫ (simplicialScheme G).δ i :=
  sorry

/-- The associated simplicial scheme is 2-coskeletal, i.e. `X = cosk₂ sk₂ X`. -/
instance simplicialScheme.instIsCoskeletal {S : Scheme.{u}} (G : GroupoidScheme S) :
    (simplicialScheme G).IsCoskeletal 2 := sorry

/-- The object scheme is the 0-fold fibre product. -/
theorem composable_zero {S : Scheme.{u}} (G : GroupoidScheme S) : composable G 0 = G.U := sorry

/-- The arrow scheme is the 1-fold fibre product. -/
theorem composable_one {S : Scheme.{u}} (G : GroupoidScheme S) : composable G 1 = G.R := sorry

/-- The 2-fold fibre product is `pullback s t`. -/
theorem composable_two {S : Scheme.{u}} (G : GroupoidScheme S) :
    composable G 2 = pullback G.s G.t := sorry

/-- After the degree `0`/`1` identifications, the degeneracy `σ 0` is the identity-arrow map `e`. -/
theorem degeneracy_zero_afterIso {S : Scheme.{u}} (G : GroupoidScheme S) :
    (degreeZero.iso G).inv ≫ (simplicialScheme G).σ 0 ≫ (degreeOne.iso G).hom = G.e.left :=
  sorry

/-- After the degree `1`/`0` identifications, the face `δ 0` is the source map `s`. -/
theorem face_one_zero_afterIso {S : Scheme.{u}} (G : GroupoidScheme S) :
    (degreeOne.iso G).inv ≫ (simplicialScheme G).δ 0 ≫ (degreeZero.iso G).hom = G.s.left :=
  sorry

/-- After the degree `1`/`0` identifications, the face `δ 1` is the target map `t`. -/
theorem face_one_one_afterIso {S : Scheme.{u}} (G : GroupoidScheme S) :
    (degreeOne.iso G).inv ≫ (simplicialScheme G).δ 1 ≫ (degreeZero.iso G).hom = G.t.left :=
  sorry

/-- After the degree `1`/`2` identifications, the degeneracy `σ 0` is `(e ∘ t, 1)`. -/
theorem degeneracy_one_zero_afterIso {S : Scheme.{u}} (G : GroupoidScheme S) :
    (degreeOne.iso G).inv ≫ (simplicialScheme G).σ 0 ≫ (degreeTwo.iso G).hom =
      (degeneracy_one_zero G).left :=
  sorry

/-- After the degree `1`/`2` identifications, the degeneracy `σ 1` is `(1, e ∘ s)`. -/
theorem degeneracy_one_one_afterIso {S : Scheme.{u}} (G : GroupoidScheme S) :
    (degreeOne.iso G).inv ≫ (simplicialScheme G).σ 1 ≫ (degreeTwo.iso G).hom =
      (degeneracy_one_one G).left :=
  sorry

/-- After the degree `2`/`1` identifications, the face `δ 0` is the earlier-arrow projection
`pullback.snd`. -/
theorem face_two_zero_afterIso {S : Scheme.{u}} (G : GroupoidScheme S) :
    (degreeTwo.iso G).inv ≫ (simplicialScheme G).δ 0 ≫ (degreeOne.iso G).hom =
      (pullback.snd G.s G.t).left :=
  sorry

/-- After the degree `2`/`1` identifications, the face `δ 1` is the composition map `c`. -/
theorem face_two_one_afterIso {S : Scheme.{u}} (G : GroupoidScheme S) :
    (degreeTwo.iso G).inv ≫ (simplicialScheme G).δ 1 ≫ (degreeOne.iso G).hom = G.c.left :=
  sorry

/-- After the degree `2`/`1` identifications, the face `δ 2` is the later-arrow projection
`pullback.fst`. -/
theorem face_two_two_afterIso {S : Scheme.{u}} (G : GroupoidScheme S) :
    (degreeTwo.iso G).inv ≫ (simplicialScheme G).δ 2 ≫ (degreeOne.iso G).hom =
      (pullback.fst G.s G.t).left :=
  sorry

/-- The zeroth face drops the later-most factor. -/
theorem face_zero_π {S : Scheme.{u}} (G : GroupoidScheme S) (n : ℕ) (i : Fin n) :
    composable.face G n 0 ≫ composableπ G n i = composableπ G (n + 1) i.succ :=
  sorry

/-- The last face drops the earlier-most factor. -/
theorem face_last_π {S : Scheme.{u}} (G : GroupoidScheme S) (n : ℕ) (i : Fin n) :
    composable.face G n (Fin.last (n + 1)) ≫ composableπ G n i =
      composableπ G (n + 1) i.castSucc :=
  sorry

/-- An interior face copies factors before the composed slot. -/
theorem face_interior_π_lt {S : Scheme.{u}} (G : GroupoidScheme S)
    (n : ℕ) (j : Fin (n + 2)) (k : Fin n)
    (hj0 : 0 < (j : ℕ)) (hjn : (j : ℕ) < n + 1) (hk : (k : ℕ) < (j : ℕ) - 1) :
    composable.face G n j ≫ composableπ G n k =
      composableπ G (n + 1) k.castSucc :=
  sorry

/-- An interior face composes the two adjacent factors through `G.compose`. -/
theorem face_interior_π_eq {S : Scheme.{u}} (G : GroupoidScheme S)
    (n : ℕ) (j : Fin (n + 2)) (k : Fin n)
    (hj0 : 0 < (j : ℕ)) (hjn : (j : ℕ) < n + 1) (hk : (k : ℕ) = (j : ℕ) - 1) :
    composable.face G n j ≫ composableπ G n k =
      G.compose (composableπ G (n + 1) k.castSucc) (composableπ G (n + 1) k.succ)
        (composableπ_adjacent G n k) :=
  sorry

/-- An interior face copies factors after the composed slot, shifting the later-first index. -/
theorem face_interior_π_gt {S : Scheme.{u}} (G : GroupoidScheme S)
    (n : ℕ) (j : Fin (n + 2)) (k : Fin n)
    (hj0 : 0 < (j : ℕ)) (hjn : (j : ℕ) < n + 1) (hk : (j : ℕ) - 1 < (k : ℕ)) :
    composable.face G n j ≫ composableπ G n k =
      composableπ G (n + 1) k.succ :=
  sorry

end AlgebraicGeometry.GroupoidScheme
