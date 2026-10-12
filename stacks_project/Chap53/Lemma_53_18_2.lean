/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.GeometricGenus.Invariance
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 53.18.2 (1): the geometric genus of a proper scheme of dimension at most one
over a field equals that of its reduction. -/
@[stacks 0CE2] #check (AlgebraicGeometry.GeometricGenus.ofScheme_eq_reduction :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1),
    AlgebraicGeometry.GeometricGenus.ofScheme X hdim =
      AlgebraicGeometry.GeometricGenus.ofScheme (Over.reduction X)
        ((Scheme.topologicalKrullDim_reduction X.left).le.trans hdim))

/- Lemma 53.18.2 (2): geometric genus is invariant under a proper birational morphism
to a proper scheme of dimension at most one over a field. -/
@[stacks 0CE2] #check (AlgebraicGeometry.GeometricGenus.ofScheme_eq_of_isProper_isBirational :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) {X' : Scheme.{u}}
    (f : X' ⟶ X.left) [IsProper f] [IsBirational f],
    AlgebraicGeometry.GeometricGenus.ofScheme (Over.mk (f ≫ X.hom) : SchemeOverField k)
        (Scheme.Hom.ProperBirational.topologicalKrullDim_le_one k X.hom f hdim :
          topologicalKrullDim X' ≤ 1) =
      AlgebraicGeometry.GeometricGenus.ofScheme X hdim)

/- Lemma 53.18.2 (3): the geometric genus of a proper scheme of dimension at most one
over a field equals that of its normalization. -/
@[stacks 0CE2] #check (AlgebraicGeometry.GeometricGenus.ofScheme_normalization_eq :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1),
    AlgebraicGeometry.GeometricGenus.ofScheme (SchemeOverField.normalization X)
        ((SchemeOverField.Normalization.topologicalKrullDim_eq X).le.trans hdim) =
      AlgebraicGeometry.GeometricGenus.ofScheme X hdim)
