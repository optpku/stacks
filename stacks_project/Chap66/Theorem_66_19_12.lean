/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Sheafification
public import stacks_project.Chap66.Lemma_66_19_7_Point

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

@[expose] public section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GeometricPoint

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Theorem 66.19.12 (1): a map of étale sheaves of sets on `X` is injective iff it is
injective on stalks at every geometric point of `X`. -/
@[stacks 04K5]
theorem sheafTypeMap_mono_iff_stalk {F G : Sheaf (smallEtaleTopology X) (Type (u + 1))}
    (a : F ⟶ G) :
    Mono a ↔ ∀ xbar : GeometricPoint X,
      Function.Injective
        (ConcreteCategory.hom ((toSmallEtalePoint xbar).sheafFiber.map a)) :=
  sorry

/-- Theorem 66.19.12 (2): a map of étale sheaves of sets on `X` is surjective iff it is
surjective on stalks at every geometric point of `X`. -/
@[stacks 04K5]
theorem sheafTypeMap_epi_iff_stalk {F G : Sheaf (smallEtaleTopology X) (Type (u + 1))}
    (a : F ⟶ G) :
    Epi a ↔ ∀ xbar : GeometricPoint X,
      Function.Surjective
        (ConcreteCategory.hom ((toSmallEtalePoint xbar).sheafFiber.map a)) :=
  sorry

/-- Theorem 66.19.12 (3): a sequence of abelian sheaves on `X_étale` is exact iff
it is exact on stalks at every geometric point of `X`. -/
@[stacks 04K5]
theorem sheafAbelian_exact_iff_stalk
    (C : ShortComplex (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})) :
    C.Exact ↔ ∀ xbar : GeometricPoint X,
      (((toSmallEtalePoint xbar).sheafFiber :
          _ ⥤ AddCommGrpCat.{u + 1}).mapShortComplex.obj C).Exact :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.GeometricPoint
