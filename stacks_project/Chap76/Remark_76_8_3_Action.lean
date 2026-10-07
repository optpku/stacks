module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import ReasLib.AlgebraicGeometry.Scheme.Gluing.DoubleAlong
public import stacks_project.Chap65.Example_65_14_1_Space
public import stacks_project.Chap67.Remark_67_19_4_Morphism

/-!
# The affine line with zero doubled, as a scheme over `Spec k`

This module records the source-facing scheme `Y` of Remark 76.8.3: the affine line
with zero doubled, obtained by gluing two copies of `𝔸¹_k` along `D(x)`, together
with its two affine charts and the comparison `1 ⨿ (-1)` toward `𝔸¹_k`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DoubledAffineLine

/-- The base scheme `S = Spec k`. -/
abbrev base (k : Type u) [Field k] : Scheme.{u} := AffineLineInvolution.base k

/-- The base scheme is the spectrum of `k`. -/
theorem base_eq (k : Type u) [Field k] :
    base k = AffineLineInvolution.base k := sorry

/-- The affine line with zero doubled, as a scheme. -/
abbrev doubledScheme (k : Type u) [Field k] : Scheme.{u} :=
  doubleAlong (AffineLineInvolution.puncturedOpen k)

/-- `doubledScheme k` is `𝔸¹_k` doubled along `D(x)`. -/
theorem doubledScheme_eq (k : Type u) [Field k] :
    doubledScheme k = doubleAlong (AffineLineInvolution.puncturedOpen k) := sorry

/-- Each canonical chart of the doubled line is compatible with the structure morphism. -/
theorem chartMap_w (k : Type u) [Field k] (i : Fin 2) :
    DoubleAlong.chartMap (AffineLineInvolution.puncturedOpen k) i ≫
        DoubleAlong.fold (AffineLineInvolution.puncturedOpen k) ≫
          (AffineLineInvolution.cover k).hom =
      (AffineLineInvolution.cover k).hom := sorry

/-- The affine line with zero doubled, as a scheme over `Spec k`. -/
def cover (k : Type u) [Field k] : Over (base k) :=
  Over.mk (DoubleAlong.fold (AffineLineInvolution.puncturedOpen k) ≫
    (AffineLineInvolution.cover k).hom)

/-- The underlying scheme of `cover k` is the doubled affine line. -/
theorem cover_left (k : Type u) [Field k] :
    (cover k).left = doubledScheme k := sorry

/-- The structure morphism of `cover k` is the fold followed by `𝔸¹_k ⟶ Spec k`. -/
theorem cover_hom (k : Type u) [Field k] :
    (cover k).hom =
      DoubleAlong.fold (AffineLineInvolution.puncturedOpen k) ≫
        (AffineLineInvolution.cover k).hom := sorry

/-- The open immersion of the `i`-th affine-line chart into the doubled line, over `Spec k`. -/
def chartHom (k : Type u) [Field k] (i : Fin 2) :
    AffineLineInvolution.cover k ⟶ cover k :=
  Over.homMk (DoubleAlong.chartMap (AffineLineInvolution.puncturedOpen k) i)
    (chartMap_w k i)

/-- The underlying scheme map of `chartHom k i` is the canonical doubled-scheme chart map. -/
theorem chartHom_left (k : Type u) [Field k] (i : Fin 2) :
    (chartHom k i).left =
      DoubleAlong.chartMap (AffineLineInvolution.puncturedOpen k) i := sorry

/-- The coproduct of the two affine-line charts, as a scheme over `Spec k`. -/
def chartCoproduct (k : Type u) [Field k] : Over (base k) :=
  AffineLineInvolution.cover k ⨿ AffineLineInvolution.cover k

/-- `chartCoproduct k` is the binary coproduct of two copies of `𝔸¹_k`. -/
theorem chartCoproduct_eq (k : Type u) [Field k] :
    chartCoproduct k =
      (AffineLineInvolution.cover k ⨿ AffineLineInvolution.cover k) := sorry

/-- The two chart immersions, as a morphism from the coproduct of charts to `Y`. -/
def atlasCoproduct (k : Type u) [Field k] : chartCoproduct k ⟶ cover k :=
  coprod.desc (chartHom k 0) (chartHom k 1)

/-- `atlasCoproduct` is the coproduct fold of the two chart immersions. -/
theorem atlasCoproduct_eq (k : Type u) [Field k] :
    atlasCoproduct k = coprod.desc (chartHom k 0) (chartHom k 1) := sorry

/-- The map `1 ⨿ (-1)` from the coproduct of charts to `𝔸¹_k`. -/
def toAffineCoproduct (k : Type u) [Field k] :
    chartCoproduct k ⟶ AffineLineInvolution.cover k :=
  coprod.desc (𝟙 _) (AffineLineInvolution.involution k)

/-- `toAffineCoproduct` is the coproduct fold of the identity and coordinatewise negation. -/
theorem toAffineCoproduct_eq (k : Type u) [Field k] :
    toAffineCoproduct k =
      coprod.desc (𝟙 (AffineLineInvolution.cover k))
        (AffineLineInvolution.involution k) := sorry

end AlgebraicGeometry.AlgebraicSpace.DoubledAffineLine
