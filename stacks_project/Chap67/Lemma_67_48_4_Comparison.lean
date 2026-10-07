module

public import Mathlib.AlgebraicGeometry.Normalization
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Definition_67_48_3_Normalization
public import stacks_project.Chap67.Lemma_67_48_8_Normalization

/-!
# Scheme comparison for relative normalization of algebraic spaces

If `X` and `Y` are schemes over `S`, the algebraic-space relative
normalization of `ofOverMap f` is represented by the scheme-level relative
normalization `Scheme.Hom.normalization f.left` of Morphisms 29.53.
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
  sorry

/-- The structure morphism of `ofOverNormalization f` is
`Scheme.Hom.fromNormalization f.left` over `S`. -/
theorem ofOverNormalization_hom {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    [AlgebraicGeometry.QuasiCompact f.left]
    [AlgebraicGeometry.QuasiSeparated f.left] :
    (ofOverNormalization f).hom = Scheme.Hom.fromNormalization f.left ≫ Y.hom :=
  sorry

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
  sorry

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
normalization of `ofOverMap f` is the scheme-level relative normalization of
Morphisms 29.53, viewed via `ofOver`. -/
theorem isNormalization_ofOverMap {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    [AlgebraicGeometry.QuasiCompact f.left]
    [AlgebraicGeometry.QuasiSeparated f.left] :
    IsNormalization (ofOverMap f) (ofOverToNormalization f)
      (ofOverFromNormalization f) :=
  sorry

/-- The constructed scheme-level relative normalization is the unique comparison
target for `Hom.normalization (ofOverMap f)`. -/
theorem existsUnique_hom_normalization_ofOver {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y) [AlgebraicGeometry.QuasiCompact f.left]
    [AlgebraicGeometry.QuasiSeparated f.left]
    [QuasiCompact (ofOverMap f)] [QuasiSeparated (ofOverMap f)] :
    ∃! h : Hom.normalization (ofOverMap f) ⟶ ofOver (ofOverNormalization f),
      Hom.toNormalization (ofOverMap f) ≫ h = ofOverToNormalization f ∧
        h ≫ ofOverFromNormalization f = Hom.fromNormalization (ofOverMap f) :=
  sorry


end AlgebraicGeometry.AlgebraicSpace

