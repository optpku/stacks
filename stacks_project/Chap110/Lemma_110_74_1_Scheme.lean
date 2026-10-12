/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Ideal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.Scheme.Gluing.DoubleAlong
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Spec
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation

/-!
# The non-separated finite-type algebraization example

Two copies of `Spec(k⟦t⟧[x])` are glued along `D(x) ∪ D(t)`, yielding a finite-type
morphism to `Spec(k⟦t⟧)` that is not separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.NonseparatedAlgebraization

/-- The coefficient ring `A = k⟦t⟧`. -/
abbrev powerSeriesRing (k : Type u) [Field k] : Type u :=
  PowerSeries k

/-- Unfolding of `powerSeriesRing`. -/
theorem powerSeriesRing_eq (k : Type u) [Field k] :
    powerSeriesRing k = PowerSeries k := sorry

/-- The ideal `I = (t)` in `k⟦t⟧`. -/
def adicIdeal (k : Type u) [Field k] : Ideal (powerSeriesRing k) :=
  Ideal.span {PowerSeries.X}

/-- Unfolding of `adicIdeal`. -/
theorem adicIdeal_eq (k : Type u) [Field k] :
    adicIdeal k = Ideal.span {PowerSeries.X} := sorry

/-- The ring `k⟦t⟧` is complete for the `(t)`-adic filtration. -/
instance instIsAdicComplete_adicIdeal (k : Type u) [Field k] :
    IsAdicComplete (adicIdeal k) (powerSeriesRing k) :=
  sorry

/-- The affine chart `Spec(A[x])` with `A = k⟦t⟧`. -/
def affineLine (k : Type u) [Field k] : Scheme.{u} :=
  Spec (.of (Polynomial (powerSeriesRing k)))

/-- Unfolding of `affineLine`. -/
theorem affineLine_eq (k : Type u) [Field k] :
    affineLine k = Spec (.of (Polynomial (powerSeriesRing k))) := sorry

/-- The global section of `affineLine k` corresponding to the coordinate `x`. -/
def affineCoordinate (k : Type u) [Field k] : Γ(affineLine k, ⊤) :=
  (ΓSpecIso (.of (Polynomial (powerSeriesRing k)))).inv Polynomial.X

/-- `affineCoordinate k` is the image of `Polynomial.X` under `ΓSpecIso`. -/
theorem affineCoordinate_eq (k : Type u) [Field k] :
    affineCoordinate k =
      (ΓSpecIso (.of (Polynomial (powerSeriesRing k)))).inv Polynomial.X := sorry

/-- The global section of `affineLine k` corresponding to the parameter `t`. -/
def formalParameter (k : Type u) [Field k] : Γ(affineLine k, ⊤) :=
  (ΓSpecIso (.of (Polynomial (powerSeriesRing k)))).inv
    (Polynomial.C (PowerSeries.X : powerSeriesRing k))

/-- `formalParameter k` is the image of `Polynomial.C PowerSeries.X` under `ΓSpecIso`. -/
theorem formalParameter_eq (k : Type u) [Field k] :
    formalParameter k =
      (ΓSpecIso (.of (Polynomial (powerSeriesRing k)))).inv
        (Polynomial.C (PowerSeries.X : powerSeriesRing k)) := sorry

/-- The maximal ideal `(x, t)` of the special origin on `Spec(A[x])`. -/
def originIdeal (k : Type u) [Field k] : Ideal (Polynomial (powerSeriesRing k)) :=
  Ideal.span {Polynomial.X, Polynomial.C (PowerSeries.X : powerSeriesRing k)}

/-- Unfolding of `originIdeal`. -/
theorem originIdeal_eq (k : Type u) [Field k] :
    originIdeal k =
      Ideal.span {Polynomial.X, Polynomial.C (PowerSeries.X : powerSeriesRing k)} :=
  sorry

/-- The punctured open `D(x) ∪ D(t)`, the complement of the closed point `(x, t)`. -/
def puncturedOpen (k : Type u) [Field k] : (affineLine k).Opens :=
  (affineLine k).basicOpen (affineCoordinate k) ⊔
    (affineLine k).basicOpen (formalParameter k)

/-- Unfolding of `puncturedOpen`. -/
theorem puncturedOpen_eq (k : Type u) [Field k] :
    puncturedOpen k =
      (affineLine k).basicOpen (affineCoordinate k) ⊔
        (affineLine k).basicOpen (formalParameter k) := sorry

/-- The punctured open `D(x) ∪ D(t)` is not closed in `Spec(A[x])`. -/
theorem not_isClosed_puncturedOpen (k : Type u) [Field k] :
    ¬ IsClosed (puncturedOpen k : Set (affineLine k)) := sorry

/-- The scheme `X` obtained by doubling `Spec(A[x])` along `D(x) ∪ D(t)`. -/
def scheme (k : Type u) [Field k] : Scheme.{u} :=
  doubleAlong (puncturedOpen k)

/-- Unfolding of `scheme`. -/
theorem scheme_eq (k : Type u) [Field k] :
    scheme k = doubleAlong (puncturedOpen k) := sorry

/-- The doubled scheme `scheme k` is Noetherian. -/
instance instIsNoetherian_scheme (k : Type u) [Field k] : IsNoetherian (scheme k) :=
  sorry

/-- The open immersion of the `i`-th copy of `Spec(A[x])` into `scheme k`. -/
abbrev chartMap (k : Type u) [Field k] (i : Fin 2) : affineLine k ⟶ scheme k :=
  DoubleAlong.chartMap (puncturedOpen k) i

/-- Unfolding of `chartMap`. -/
theorem chartMap_eq (k : Type u) [Field k] (i : Fin 2) :
    chartMap k i = DoubleAlong.chartMap (puncturedOpen k) i := sorry

/-- Each canonical chart map is an open immersion. -/
instance instIsOpenImmersion_chartMap (k : Type u) [Field k] (i : Fin 2) :
    IsOpenImmersion (chartMap k i) :=
  DoubleAlong.chartMap_isOpenImmersion (puncturedOpen k) i

/-- The image of the `i`-th canonical chart in `scheme k`. -/
abbrev chart (k : Type u) [Field k] (i : Fin 2) : (scheme k).Opens :=
  DoubleAlong.chart (puncturedOpen k) i

/-- Unfolding of `chart`. -/
theorem chart_eq (k : Type u) [Field k] (i : Fin 2) :
    chart k i = DoubleAlong.chart (puncturedOpen k) i := sorry

/-- The two canonical charts cover `scheme k`. -/
theorem chart_cover (k : Type u) [Field k] : chart k 0 ⊔ chart k 1 = ⊤ := sorry

/-- The structure morphism of each affine chart, induced by `A → A[x]`. -/
def affineLineToSpec (k : Type u) [Field k] :
    affineLine k ⟶ Spec (.of (powerSeriesRing k)) :=
  Spec.map (CommRingCat.ofHom Polynomial.C)

/-- Unfolding of `affineLineToSpec`. -/
theorem affineLineToSpec_eq (k : Type u) [Field k] :
    affineLineToSpec k = Spec.map (CommRingCat.ofHom Polynomial.C) := sorry

/-- The two copies of `affineLineToSpec k` agree on `puncturedOpen k`. -/
theorem affineLineToSpec_compatible (k : Type u) [Field k] :
    (puncturedOpen k).ι ≫ affineLineToSpec k =
      (puncturedOpen k).ι ≫ affineLineToSpec k := sorry

/-- The structure morphism `X ⟶ Spec(A)` obtained by descending the two chart maps. -/
def toSpec (k : Type u) [Field k] : scheme k ⟶ Spec (.of (powerSeriesRing k)) :=
  DoubleAlong.desc (puncturedOpen k) (fun _ ↦ affineLineToSpec k) rfl

/-- Unfolding of `toSpec`. -/
theorem toSpec_eq (k : Type u) [Field k] :
    toSpec k =
      DoubleAlong.desc (puncturedOpen k) (fun _ ↦ affineLineToSpec k) rfl := sorry

/-- On each canonical chart, `toSpec k` restricts to `affineLineToSpec k`. -/
theorem toSpec_comp_chartMap (k : Type u) [Field k] (i : Fin 2) :
    chartMap k i ≫ toSpec k = affineLineToSpec k := sorry

/-- The structure morphism `toSpec k` is of finite type. -/
instance instFiniteType_toSpec (k : Type u) [Field k] :
    Scheme.Hom.FiniteType (toSpec k) :=
  sorry

/-- The structure morphism `toSpec k` is locally of finite type. -/
instance instLocallyOfFiniteType_toSpec (k : Type u) [Field k] :
    LocallyOfFiniteType (toSpec k) :=
  sorry

/-- The structure morphism `X ⟶ Spec(A)` is not separated. -/
theorem not_isSeparated (k : Type u) [Field k] : ¬ IsSeparated (toSpec k) :=
  sorry

/-- The algebraic space over `Spec(A)` presented by `scheme k`. -/
def spaceX (k : Type u) [Field k] : AlgebraicSpace (Spec (.of (powerSeriesRing k))) :=
  ofOver (Over.mk (toSpec k))

/-- Unfolding of `spaceX`. -/
theorem spaceX_eq (k : Type u) [Field k] :
    spaceX k = ofOver (Over.mk (toSpec k)) := sorry

/-- The algebraic space over `Spec(A)` presented by `Spec(A)` itself. -/
def spaceB (k : Type u) [Field k] : AlgebraicSpace (Spec (.of (powerSeriesRing k))) :=
  ofOver (Over.mk (𝟙 (Spec (.of (powerSeriesRing k)))))

/-- Unfolding of `spaceB`. -/
theorem spaceB_eq (k : Type u) [Field k] :
    spaceB k = ofOver (Over.mk (𝟙 (Spec (.of (powerSeriesRing k))))) := sorry

/-- Compatibility of `toSpec k` with the identity on `Spec(A)`. -/
theorem toSpec_comp_id (k : Type u) [Field k] :
    toSpec k ≫ 𝟙 (Spec (.of (powerSeriesRing k))) = toSpec k := sorry

/-- The morphism of algebraic spaces over `Spec(A)` presented by `toSpec k`. -/
def spaceHom (k : Type u) [Field k] : spaceX k ⟶ spaceB k :=
  ofOverHomMk (toSpec k) (Category.comp_id (toSpec k))

/-- Unfolding of `spaceHom`. -/
theorem spaceHom_eq (k : Type u) [Field k] :
    spaceHom k = ofOverHomMk (toSpec k) (Category.comp_id (toSpec k)) := sorry

/-- The algebraic-space morphism `spaceHom k` is of finite presentation. -/
instance instFinitePresentation_spaceHom (k : Type u) [Field k] :
    FinitePresentation (spaceHom k) :=
  sorry

end AlgebraicGeometry.NonseparatedAlgebraization
