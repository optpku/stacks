/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Normalization.Compactification

@[expose] public section

open AlgebraicGeometry
open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

/-
Lemma 33.43.7: a separated finite-type scheme of dimension at most one over a field has, after a
finite purely inseparable extension, a normalized base change whose finitely many irreducible
components admit compatible dense smooth projective geometrically irreducible compactifications
over finite separable extensions.
-/
@[stacks 0GK5] #check
  (AlgebraicGeometry.FieldExtension.Normalization.exists_componentCompactifications_of_dimension_le_one :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [Scheme.Hom.FiniteType f] [IsSeparated f],
      topologicalKrullDim X ≤ 1 →
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
                  Dense (U : Set Ybar))
