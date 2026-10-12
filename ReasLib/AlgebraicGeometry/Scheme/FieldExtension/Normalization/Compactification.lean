/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Normal.Normalization
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.IrreducibleComponent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Compactification
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Regularity
public import ReasLib.AlgebraicGeometry.Scheme.Normal.Regular
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections.Proper

/-!
# Compactifications of normalized field-extension components

This module records componentwise smooth projective compactifications of normalized base changes
of one-dimensional schemes after finite purely inseparable field extensions.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.FieldExtension.Normalization

/-- A separated finite-type scheme of topological Krull dimension at most one over a field has,
after a finite purely inseparable field extension, a normalized base change with finitely many
irreducible components. Each canonical reduced component has a dense open immersion into a
smooth H-projective geometrically irreducible scheme of dimension at most one over a finite
separable extension, compatibly with the normalization and structure morphisms. -/
theorem exists_componentCompactifications_of_dimension_le_one
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [Scheme.Hom.FiniteType f] [IsSeparated f] (hdim : topologicalKrullDim X ≤ 1) :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k')
      (_ : FiniteDimensional k k') (_ : IsPurelyInseparable k k'),
      let XK := FieldExtension.baseChange k k' f
      let XKOver : Over (Spec (CommRingCat.of k')) :=
        FieldExtension.Over.baseChange k k' (Over.mk f)
      let Y : Over (Spec (CommRingCat.of k')) :=
        @FieldExtension.Normalization.baseChange k _ (Over.mk f) k' _ _
          (Algebraic.ofFiniteType f)
      Finite (irreducibleComponents Y.left) ∧
        ∀ Z : irreducibleComponents Y.left,
          let YZ : Scheme.{u} := Y.left.irreducibleComponentSubscheme Z
          let iZ : YZ ⟶ Y.left := Y.left.irreducibleComponentSubschemeι Z
          let νZ : YZ ⟶ XK := iZ ≫ XK.normalizationTo
          ∃ (K : Type u) (_ : Field K) (_ : Algebra k' K)
            (_ : FiniteDimensional k' K) (_ : Algebra.IsSeparable k' K)
            (g : YZ ⟶ Spec (CommRingCat.of K))
            (Ybar : Scheme.{u}) (fbar : Ybar ⟶ Spec (CommRingCat.of K))
            (j : YZ ⟶ Ybar) (_ : IsOpenImmersion j),
            g ≫ Spec.map (CommRingCat.ofHom (algebraMap k' K)) = νZ ≫ XKOver.hom ∧
              j ≫ fbar = g ∧
              HProjective fbar ∧
              Smooth fbar ∧
              GeometricallyIrreducible fbar ∧
              topologicalKrullDim Ybar ≤ 1 ∧
              let U : Ybar.Opens := @Scheme.Hom.opensRange _ _ j inferInstance
              Dense (U : Set Ybar) := sorry

end AlgebraicGeometry.FieldExtension.Normalization
