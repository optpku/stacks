/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Truncation.Brutal.Trunc.Step
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.Morphism
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Center.NegOnePow

/-!
# Postnikov towers from brutal truncations

This leaf turns the canonical brutal truncation tower of a cochain complex into a sequential
Postnikov tower in its derived category.  The unbounded construction owns the stages and their
triangles; boundedness above at zero is needed only for the right-end isomorphism.
-/

@[expose] public section

open CategoryTheory.Pretriangulated
open DerivedCategory

noncomputable section

universe w v u

namespace CategoryTheory.CochainComplex.Brutal.Derived.Postnikov

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Shifting a cutoff piece by its cutoff degree moves its unique term to degree zero. -/
theorem index_add_zero (n : ℕ) :
    Brutal.Tower.index n + (0 : ℤ) = Brutal.Tower.index n := sorry

/-- Consecutive negative cutoffs differ by one. -/
theorem index_succ_add_one (n : ℕ) :
    Brutal.Tower.index (n + 1) + (1 : ℤ) = Brutal.Tower.index n := sorry

variable [HasDerivedCategory.{w} A]

/-- The `n`th object of the term row, concentrated in derived degree zero. -/
@[stacks 0D8Z "term object of the brutal Postnikov tower"]
noncomputable abbrev x (K : CochainComplex A ℤ) (n : ℕ) : DerivedCategory A :=
  (DerivedCategory.singleFunctor A (0 : ℤ)).obj (K.X (Brutal.Tower.index n))

/-- A cochain map induces the map between the `n`th term objects. -/
noncomputable abbrev xMap {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℕ) :
    x K n ⟶ x L n :=
  (DerivedCategory.singleFunctor A (0 : ℤ)).map (f.f (Brutal.Tower.index n))

/-- The term-object map of an identity is an identity. -/
@[simp]
theorem xMap_id (K : CochainComplex A ℤ) (n : ℕ) : xMap (𝟙 K) n = 𝟙 (x K n) := sorry

/-- Term-object maps preserve composition. -/
@[simp]
theorem xMap_comp {K L M : CochainComplex A ℤ} (f : K ⟶ L) (g : L ⟶ M) (n : ℕ) :
    xMap (f ≫ g) n = xMap f n ≫ xMap g n := sorry

/-- The differential in the derived term row. -/
@[stacks 0D8Z "differential of the brutal Postnikov row"]
noncomputable abbrev d (K : CochainComplex A ℤ) (n : ℕ) : x K (n + 1) ⟶ x K n :=
  (DerivedCategory.singleFunctor A (0 : ℤ)).map
    (K.d (Brutal.Tower.index (n + 1)) (Brutal.Tower.index n))

/-- The `n`th auxiliary object is the `n`th brutal stage shifted by its cutoff. -/
@[stacks 0D8Z "auxiliary object of the brutal Postnikov tower"]
noncomputable abbrev y (K : CochainComplex A ℤ) (n : ℕ) : DerivedCategory A :=
  (Q.obj (Trunc.obj K n))⟦Brutal.Tower.index n⟧

/-- A cochain map induces the map between the `n`th shifted brutal stages. -/
noncomputable def yMap {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℕ) :
    y K n ⟶ y L n :=
  (Q.map (Trunc.mapApp f n))⟦Brutal.Tower.index n⟧'

/-- The auxiliary-object map of an identity is an identity. -/
@[simp]
theorem yMap_id (K : CochainComplex A ℤ) (n : ℕ) : yMap (𝟙 K) n = 𝟙 (y K n) := sorry

/-- Auxiliary-object maps preserve composition. -/
@[simp]
theorem yMap_comp {K L M : CochainComplex A ℤ} (f : K ⟶ L) (g : L ⟶ M) (n : ℕ) :
    yMap (f ≫ g) n = yMap f n ≫ yMap g n := sorry

/-- The shifted cutoff piece is canonically the corresponding degree-zero term object. -/
@[stacks 0D8Z]
noncomputable def xIso (K : CochainComplex A ℤ) (n : ℕ) :
    (Q.obj (Trunc.Piece.obj K n))⟦Brutal.Tower.index n⟧ ≅ x K n :=
  ((DerivedCategory.singleFunctors A).shiftIso (Brutal.Tower.index n) 0
    (Brutal.Tower.index n) (index_add_zero n)).app (K.X (Brutal.Tower.index n))

namespace Stage

/-- The shifted and rotated derived triangle of two consecutive brutal stages. -/
@[stacks 0D8Z "triangle of consecutive brutal truncations"]
noncomputable def triangle (K : CochainComplex A ℤ) (n : ℕ) :
    Triangle (DerivedCategory A) :=
  ((shiftFunctor (Triangle (DerivedCategory A)) (Brutal.Tower.index (n + 1))).obj
    (DerivedCategory.triangleOfSES (Trunc.Step.shortExact K n))).rotate

/-- The first vertex of the stage triangle is the next auxiliary object, with the canonical
rotation sign. -/
noncomputable def leftIso (K : CochainComplex A ℤ) (n : ℕ) :
    (triangle K n).obj₁ ≅ y K (n + 1) :=
  (((-1) ^ (Brutal.Tower.index (n + 1)) : (CatCenter (DerivedCategory A))ˣ) • Iso.refl _)

/-- The third vertex of the stage triangle is the preceding auxiliary object. -/
noncomputable def rightIso (K : CochainComplex A ℤ) (n : ℕ) :
    (triangle K n).obj₃ ≅ y K n :=
  ((shiftFunctorAdd' (DerivedCategory A) (Brutal.Tower.index (n + 1)) 1
    (Brutal.Tower.index n) (index_succ_add_one n)).app (Q.obj (Trunc.obj K n))).symm

end Stage

/-- The comparison from the shifted brutal stage to its degree-zero cutoff term. -/
@[stacks 0D8Z "comparison in the brutal Postnikov tower"]
noncomputable def toX (K : CochainComplex A ℤ) (n : ℕ) : y K n ⟶ x K n :=
  (Q.map (Trunc.Piece.π K n))⟦Brutal.Tower.index n⟧' ≫ (xIso K n).hom

/-- The map from the next term object to the preceding auxiliary object. -/
@[stacks 0D8Z "second map in the brutal Postnikov triangle"]
noncomputable def toNext (K : CochainComplex A ℤ) (n : ℕ) : x K (n + 1) ⟶ y K n :=
  (xIso K (n + 1)).inv ≫ (Stage.triangle K n).mor₂ ≫ (Stage.rightIso K n).hom

/-- The connecting map between consecutive auxiliary objects. -/
@[stacks 0D8Z "connecting map in the brutal Postnikov tower"]
noncomputable def connecting (K : CochainComplex A ℤ) (n : ℕ) :
    y K n ⟶ (y K (n + 1))⟦(1 : ℤ)⟧ :=
  (Stage.rightIso K n).inv ≫ (Stage.triangle K n).mor₃ ≫
    (shiftFunctor (DerivedCategory A) (1 : ℤ)).map (Stage.leftIso K n).hom

/-- The right-end comparison is invertible when the source complex vanishes above degree zero. -/
@[stacks 0D8Z]
theorem base (K : CochainComplex A ℤ) [K.IsStrictlyLE 0] : IsIso (toX K 0) := sorry

/-- Each shifted brutal stage row is a distinguished triangle. -/
@[stacks 0D8Z]
theorem distinguished (K : CochainComplex A ℤ) (n : ℕ) :
    Triangle.mk (toX K (n + 1)) (toNext K n) (connecting K n) ∈
      distTriang (DerivedCategory A) := sorry

/-- The two finite edges of a stage triangle recover the differential of the term row. -/
@[reassoc, stacks 0D8Z]
theorem comp (K : CochainComplex A ℤ) (n : ℕ) :
    toNext K n ≫ toX K n = d K n := sorry

/-- The term-row differential is natural in the source complex. -/
@[reassoc, stacks 0D8Z]
theorem d_naturality {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℕ) :
    d K n ≫ xMap f n = xMap f (n + 1) ≫ d L n := sorry

/-- The stage-to-term comparison is natural in the source complex. -/
@[reassoc, stacks 0D8Z]
theorem toX_naturality {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℕ) :
    toX K n ≫ xMap f n = yMap f n ≫ toX L n := sorry

/-- The second stage map is natural in the source complex. -/
@[reassoc, stacks 0D8Z]
theorem toNext_naturality {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℕ) :
    toNext K n ≫ yMap f n = xMap f (n + 1) ≫ toNext L n := sorry

/-- The connecting map is natural in the source complex. -/
@[reassoc, stacks 0D8Z]
theorem connecting_naturality {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℕ) :
    connecting K n ≫ (shiftFunctor (DerivedCategory A) (1 : ℤ)).map (yMap f (n + 1)) =
      yMap f n ≫ connecting L n := sorry

/-- The sequential Postnikov tower canonically attached to a complex concentrated in degrees
at most zero. -/
@[stacks 0D8Z "Postnikov tower of a bounded-above cochain complex"]
noncomputable def tower (K : CochainComplex A ℤ) [K.IsStrictlyLE 0] :
    PostnikovSystem.Tower (DerivedCategory A) where
  X := x K
  d := d K
  Y := y K
  toX := toX K
  toNext := toNext K
  connecting := connecting K
  base := base K
  distinguished := distinguished K
  comp := comp K

/-- A cochain map between complexes concentrated in degrees at most zero induces a morphism of
their canonical Postnikov towers. -/
@[stacks 0D8Z "functoriality of the brutal Postnikov tower"]
noncomputable def map {K L : CochainComplex A ℤ} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0]
    (f : K ⟶ L) : (tower K).Hom (tower L) :=
  PostnikovSystem.Tower.Hom.homMk (xMap f) (yMap f) (d_naturality f)
    (toX_naturality f) (toNext_naturality f) (connecting_naturality f)

/-- The row-object component of the induced tower morphism is the canonical term-object map. -/
@[simp, stacks 0D8Z]
theorem map_xMap {K L : CochainComplex A ℤ} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0]
    (f : K ⟶ L) (n : ℕ) : (map f).xMap n = xMap f n := sorry

/-- The auxiliary component of the induced tower morphism is the shifted truncation map. -/
@[simp, stacks 0D8Z]
theorem map_yMap {K L : CochainComplex A ℤ} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0]
    (f : K ⟶ L) (n : ℕ) : (map f).yMap n = yMap f n := sorry

/-- The identity cochain map induces the identity tower morphism. -/
@[simp]
theorem map_id (K : CochainComplex A ℤ) [K.IsStrictlyLE 0] :
    map (𝟙 K) = PostnikovSystem.Tower.Hom.id (tower K) := sorry

/-- The tower morphism construction preserves composition. -/
@[simp]
theorem map_comp {K L M : CochainComplex A ℤ}
    [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] [M.IsStrictlyLE 0]
    (f : K ⟶ L) (g : L ⟶ M) :
    map (f ≫ g) = PostnikovSystem.Tower.Hom.comp (map f) (map g) := sorry

namespace Finite

/-- The tower index represented by a position in a reversed finite row. -/
abbrev index {n : ℕ} (i : Fin n) : ℕ := PostnikovSystem.Tower.Finite.index i

/-- The reversed finite row cut out from the brutal Postnikov tower. -/
@[stacks 0D8Z "finite row of the brutal Postnikov tower"]
noncomputable abbrev row (K : CochainComplex A ℤ) [K.IsStrictlyLE 0] (n : ℕ) :=
  (tower K).row n

/-- The finite Postnikov system cut out from the brutal Postnikov tower. -/
@[stacks 0D8Z "finite brutal Postnikov system"]
noncomputable abbrev system (K : CochainComplex A ℤ) [K.IsStrictlyLE 0] (n : ℕ) :=
  (tower K).finite n

/-- A cochain map induces a morphism between every pair of finite brutal Postnikov systems. -/
@[stacks 0D8Z]
noncomputable abbrev map {K L : CochainComplex A ℤ}
    [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (f : K ⟶ L) (n : ℕ) :=
  (Postnikov.map f).finite n

/-- A finite-row object is the corresponding degree-zero term object. -/
@[simp, stacks 0D8Z]
theorem rowObj (K : CochainComplex A ℤ) [K.IsStrictlyLE 0]
    (n : ℕ) (i : Fin (n + 1)) : (row K n).obj i = x K (index i) := sorry

/-- A finite-system auxiliary object is the corresponding shifted brutal stage. -/
@[simp, stacks 0D8Z]
theorem auxObj (K : CochainComplex A ℤ) [K.IsStrictlyLE 0]
    (n : ℕ) (i : Fin (n + 1)) : system K n i = y K (index i) := sorry

/-- A component of the induced finite-row morphism is the corresponding term-object map. -/
@[simp, stacks 0D8Z]
theorem map_row_app {K L : CochainComplex A ℤ}
    [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (f : K ⟶ L)
    (n : ℕ) (i : Fin (n + 1)) :
    ((Postnikov.map f).row n).app i =
      eqToHom (rowObj K n i) ≫ xMap f (index i) ≫ eqToHom (rowObj L n i).symm := sorry

/-- An auxiliary component of the induced finite-system morphism is the corresponding shifted
truncation map. -/
@[simp, stacks 0D8Z]
theorem map_yMap {K L : CochainComplex A ℤ}
    [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (f : K ⟶ L)
    (n : ℕ) (i : Fin (n + 1)) :
    (map f n).yMap i =
      eqToHom (auxObj K n i) ≫ yMap f (index i) ≫ eqToHom (auxObj L n i).symm := sorry

/-- The source of a finite-row arrow is the next term object. -/
@[simp]
theorem rowSource (K : CochainComplex A ℤ) [K.IsStrictlyLE 0]
    (n : ℕ) (i : Fin n) : (row K n).obj i.castSucc = x K (index i + 1) := sorry

/-- The target of a finite-row arrow is its indexed term object. -/
@[simp]
theorem rowTarget (K : CochainComplex A ℤ) [K.IsStrictlyLE 0]
    (n : ℕ) (i : Fin n) : (row K n).obj i.succ = x K (index i) := sorry

/-- The source auxiliary object of a finite stage is the next shifted brutal stage. -/
@[simp]
theorem auxSource (K : CochainComplex A ℤ) [K.IsStrictlyLE 0]
    (n : ℕ) (i : Fin n) : system K n i.castSucc = y K (index i + 1) := sorry

/-- The target auxiliary object of a finite stage is its indexed shifted brutal stage. -/
@[simp]
theorem auxTarget (K : CochainComplex A ℤ) [K.IsStrictlyLE 0]
    (n : ℕ) (i : Fin n) : system K n i.succ = y K (index i) := sorry

/-- A finite-row map is the corresponding differential, up to endpoint transports. -/
@[stacks 0D8Z]
theorem rowMap (K : CochainComplex A ℤ) [K.IsStrictlyLE 0]
    (n : ℕ) (i : Fin n) :
    (row K n).map' i.1 (i.1 + 1) =
      eqToHom (rowSource K n i) ≫ d K (index i) ≫
        eqToHom (rowTarget K n i).symm := sorry

/-- A finite-system comparison is the corresponding tower comparison. -/
@[stacks 0D8Z]
theorem toX (K : CochainComplex A ℤ) [K.IsStrictlyLE 0]
    (n : ℕ) (i : Fin (n + 1)) :
    (system K n).toX i =
      eqToHom (auxObj K n i) ≫
        _root_.CategoryTheory.CochainComplex.Brutal.Derived.Postnikov.toX K (index i) ≫
          eqToHom (rowObj K n i).symm := sorry

/-- A finite-system second map is the corresponding tower map. -/
@[stacks 0D8Z]
theorem toNext (K : CochainComplex A ℤ) [K.IsStrictlyLE 0]
    (n : ℕ) (i : Fin n) :
    (system K n).toNext i =
      eqToHom (rowSource K n i) ≫
        _root_.CategoryTheory.CochainComplex.Brutal.Derived.Postnikov.toNext K (index i) ≫
          eqToHom (auxTarget K n i).symm := sorry

/-- A finite-system connecting map is the corresponding tower connecting map. -/
@[stacks 0D8Z]
theorem connecting (K : CochainComplex A ℤ) [K.IsStrictlyLE 0]
    (n : ℕ) (i : Fin n) :
    (system K n).connecting i =
      eqToHom (auxTarget K n i) ≫
        _root_.CategoryTheory.CochainComplex.Brutal.Derived.Postnikov.connecting K
          (index i) ≫ (eqToHom (auxSource K n i).symm)⟦(1 : ℤ)⟧' := sorry

/-- Every triangle in a finite brutal Postnikov system is distinguished. -/
@[stacks 0D8Z]
theorem distinguished (K : CochainComplex A ℤ) [K.IsStrictlyLE 0]
    (n : ℕ) (i : Fin n) : (system K n).triangle i ∈ distTriang (DerivedCategory A) := sorry

/-- Every finite term row cut out from a brutal Postnikov tower is a complex. -/
@[stacks 0D8Z]
theorem isComplex (K : CochainComplex A ℤ) [K.IsStrictlyLE 0] (n : ℕ) :
    (row K n).IsComplex := sorry

end Finite

end CategoryTheory.CochainComplex.Brutal.Derived.Postnikov
