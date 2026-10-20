module

public import Mathlib.AlgebraicGeometry.Normalization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization

/-!
# Scheme comparison for relative normalization of algebraic spaces

If `X` and `Y` are schemes over `S`, the algebraic-space relative
normalization of `ofOverMap f` is represented by the scheme-level relative
normalization `Scheme.Hom.normalization f.left`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The scheme-level relative normalization of `f.left`, viewed as a scheme over
`S` via `Scheme.Hom.fromNormalization f.left ≫ Y.hom`. -/
def ofOverNormalization {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    [AlgebraicGeometry.QuasiCompact f.left]
    [AlgebraicGeometry.QuasiSeparated f.left] : Over S :=
  Over.mk (Scheme.Hom.fromNormalization f.left ≫ Y.hom)

/-- The underlying scheme of `ofOverNormalization f` is the scheme-level
relative normalization of `f.left`. -/
theorem ofOverNormalization_left {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    [AlgebraicGeometry.QuasiCompact f.left]
    [AlgebraicGeometry.QuasiSeparated f.left] :
    (ofOverNormalization f).left = Scheme.Hom.normalization f.left :=
  rfl

/-- The structure morphism of `ofOverNormalization f` is
`Scheme.Hom.fromNormalization f.left` over `S`. -/
theorem ofOverNormalization_hom {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    [AlgebraicGeometry.QuasiCompact f.left]
    [AlgebraicGeometry.QuasiSeparated f.left] :
    (ofOverNormalization f).hom = Scheme.Hom.fromNormalization f.left ≫ Y.hom :=
  rfl

/-- `Scheme.Hom.toNormalization f.left` is a morphism over `S` into
`ofOverNormalization f`. -/
theorem ofOverToNormalization_w {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    [AlgebraicGeometry.QuasiCompact f.left]
    [AlgebraicGeometry.QuasiSeparated f.left] :
    Scheme.Hom.toNormalization f.left ≫ (ofOverNormalization f).hom = X.hom :=
  sorry

/-- `Scheme.Hom.fromNormalization f.left` is a morphism over `S` from
`ofOverNormalization f` to `Y`. -/
theorem ofOverFromNormalization_w {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    [AlgebraicGeometry.QuasiCompact f.left]
    [AlgebraicGeometry.QuasiSeparated f.left] :
    Scheme.Hom.fromNormalization f.left ≫ Y.hom = (ofOverNormalization f).hom :=
  rfl

/-- The algebraic-space morphism `ofOver X ⟶ ofOver (ofOverNormalization f)`
induced by the scheme-level `toNormalization`. -/
def ofOverToNormalization {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    [AlgebraicGeometry.QuasiCompact f.left]
    [AlgebraicGeometry.QuasiSeparated f.left] :
    ofOver X ⟶ ofOver (ofOverNormalization f) :=
  ofOverMap (Over.homMk (Scheme.Hom.toNormalization f.left) (ofOverToNormalization_w f))

/-- The algebraic-space morphism `ofOver (ofOverNormalization f) ⟶ ofOver Y`
induced by the scheme-level `fromNormalization`. -/
def ofOverFromNormalization {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    [AlgebraicGeometry.QuasiCompact f.left]
    [AlgebraicGeometry.QuasiSeparated f.left] :
    ofOver (ofOverNormalization f) ⟶ ofOver Y :=
  ofOverMap (Over.homMk (Scheme.Hom.fromNormalization f.left)
    (ofOverFromNormalization_w f))

/-- When `X` and `Y` are representable, the algebraic-space relative
normalization of `ofOverMap f` is the scheme-level relative normalization,
viewed via `ofOver`. -/
theorem isNormalization_ofOverMap {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    [AlgebraicGeometry.QuasiCompact f.left]
    [AlgebraicGeometry.QuasiSeparated f.left] :
    IsNormalization (ofOverMap f) (ofOverToNormalization f)
      (ofOverFromNormalization f) :=
  sorry

/-- Every relative-normalization factorization of a morphism of schemes is uniquely
isomorphic to the scheme-level relative normalization, compatibly with both
factorization maps. -/
theorem existsUnique_iso_ofOverNormalization {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y) [AlgebraicGeometry.QuasiCompact f.left]
    [AlgebraicGeometry.QuasiSeparated f.left]
    {N : AlgebraicSpace S} (toN : ofOver X ⟶ N) (fromN : N ⟶ ofOver Y)
    (hN : IsNormalization (ofOverMap f) toN fromN) :
    ∃! e : N ≅ ofOver (ofOverNormalization f),
      toN ≫ e.hom = ofOverToNormalization f ∧
        e.hom ≫ ofOverFromNormalization f = fromN :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
