/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.IrreducibleComponents
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Nagata
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Normalization.GenericPoints
public import ReasLib.AlgebraicGeometry.Scheme.Variety
public import ReasLib.RingTheory.Normal.Nagata.Field

/-!
# Normalization of schemes locally of finite type over a field

This module packages absolute normalization as a scheme over the same field and records its
finiteness, component decomposition, and preservation properties.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- The normalization of a scheme over a field, with structure morphism induced through the
normalization morphism. -/
noncomputable def normalization
    (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    [QuasiCompact (genericPointSpectrumCoproductTo X.left)]
    [QuasiSeparated (genericPointSpectrumCoproductTo X.left)] : SchemeOverField k :=
  Over.mk (X.left.normalizationTo ≫ X.hom)

namespace Normalization

/-- A scheme locally of finite type over a field is a Nagata scheme. -/
instance instNagata (X : SchemeOverField k) [LocallyOfFiniteType X.hom] :
    Scheme.Nagata X.left := sorry

/-- The normalization morphism of a scheme locally of finite type over a field is finite. -/
instance instIsFiniteNormalizationTo
    (X : SchemeOverField k) [LocallyOfFiniteType X.hom] :
    IsFinite X.left.normalizationTo := sorry

/-- The normalization morphism of a scheme locally of finite type over a field is dominant. -/
instance instIsDominantNormalizationTo
    (X : SchemeOverField k) [LocallyOfFiniteType X.hom] :
    IsDominant X.left.normalizationTo := sorry

/-- The normalization of a reduced irreducible-component subscheme, equipped with its canonical
structure morphism to the base field. -/
noncomputable def irreducibleComponentNormalization
    (X : SchemeOverField k) (Z : irreducibleComponents X.left)
    [QuasiCompact (genericPointSpectrumCoproductTo
      (X.left.irreducibleComponentSubscheme Z))]
    [QuasiSeparated (genericPointSpectrumCoproductTo
      (X.left.irreducibleComponentSubscheme Z))] : SchemeOverField k :=
  Over.mk (((X.left.irreducibleComponentSubscheme Z).normalizationTo ≫
    X.left.irreducibleComponentSubschemeι Z) ≫ X.hom)

/-- The normalization is the coproduct of the normalizations of its reduced irreducible-component
subschemes, compatibly with their canonical morphisms to the original scheme. -/
theorem normalizationIsoCoproductIrreducibleComponentNormalizations
    (X : SchemeOverField k) [LocallyOfFiniteType X.hom] :
    ∃ e :
        (∐ fun Z : irreducibleComponents X.left ↦
          (irreducibleComponentNormalization X Z).left) ≅
            X.left.normalization,
      Limits.Sigma.desc (fun Z : irreducibleComponents X.left ↦
          (X.left.irreducibleComponentSubscheme Z).normalizationTo ≫
            X.left.irreducibleComponentSubschemeι Z) =
        e.hom ≫ X.left.normalizationTo := sorry

/-- Each normalized reduced irreducible-component subscheme is normal. -/
theorem isNormal_irreducibleComponentNormalization
    (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (Z : irreducibleComponents X.left) :
    Scheme.isNormal (irreducibleComponentNormalization X Z).left := sorry

/-- Each normalized reduced irreducible-component subscheme is irreducible. -/
instance instIrreducibleSpaceIrreducibleComponentNormalization
    (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (Z : irreducibleComponents X.left) :
    IrreducibleSpace (irreducibleComponentNormalization X Z).left := sorry

/-- The normalization of a locally algebraic scheme over a field is locally algebraic. -/
instance instLocallyAlgebraicNormalization
    (X : SchemeOverField k) [LocallyAlgebraic X] :
    LocallyAlgebraic (SchemeOverField.normalization X) := sorry

/-- The normalization of an algebraic scheme over a field is algebraic. -/
instance instAlgebraicNormalization
    (X : SchemeOverField k) [Algebraic X] :
    Algebraic (SchemeOverField.normalization X) := sorry

/-- Each normalized reduced irreducible-component subscheme of a locally algebraic scheme is
locally algebraic over the same field. -/
instance instLocallyAlgebraicIrreducibleComponentNormalization
    (X : SchemeOverField k) [LocallyAlgebraic X]
    (Z : irreducibleComponents X.left) :
    LocallyAlgebraic (irreducibleComponentNormalization X Z) := sorry

/-- The normalization morphism of a reduced algebraic scheme over a field is birational. -/
instance instIsBirationalNormalizationToOfIsReducedAlgebraic
    (X : SchemeOverField k) [Algebraic X] [IsReduced X.left] :
    IsBirational X.left.normalizationTo := sorry

/-- The normalization of a variety over a field is a variety over the same field. -/
instance instVarietyNormalization
    (X : SchemeOverField k) [Variety X] :
    Variety (SchemeOverField.normalization X) := sorry

/-- The normalization morphism of a variety over a field is birational. -/
instance instIsBirationalNormalizationToOfVariety
    (X : SchemeOverField k) [Variety X] :
    IsBirational X.left.normalizationTo := sorry

end Normalization

end AlgebraicGeometry.SchemeOverField
