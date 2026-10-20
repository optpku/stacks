/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.StalkDetection
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GeometricPoint

/- Theorem 66.19.12 (1): a map of étale sheaves of sets on `X` is injective iff it is
injective on stalks at every geometric point of `X`. -/
@[stacks 04K5] #check
  (AlgebraicGeometry.AlgebraicSpace.GeometricPoint.sheafTypeMap_mono_iff_stalk :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      {F G : Sheaf (smallEtaleTopology X) (Type (u + 1))} (a : F ⟶ G),
    Mono a ↔ ∀ xbar : GeometricPoint X,
      Function.Injective
        (ConcreteCategory.hom ((toSmallEtalePoint xbar).sheafFiber.map a)))

/- Theorem 66.19.12 (2): a map of étale sheaves of sets on `X` is surjective iff it is
surjective on stalks at every geometric point of `X`. -/
@[stacks 04K5] #check
  (AlgebraicGeometry.AlgebraicSpace.GeometricPoint.sheafTypeMap_epi_iff_stalk :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      {F G : Sheaf (smallEtaleTopology X) (Type (u + 1))} (a : F ⟶ G),
    Epi a ↔ ∀ xbar : GeometricPoint X,
      Function.Surjective
        (ConcreteCategory.hom ((toSmallEtalePoint xbar).sheafFiber.map a)))

/- Theorem 66.19.12 (3): a sequence of abelian sheaves on `X_étale` is exact iff
it is exact on stalks at every geometric point of `X`. -/
@[stacks 04K5] #check
  (AlgebraicGeometry.AlgebraicSpace.GeometricPoint.sheafAbelian_exact_iff_stalk :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      (C : ShortComplex (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})),
    C.Exact ↔ ∀ xbar : GeometricPoint X,
      (((toSmallEtalePoint xbar).sheafFiber :
          _ ⥤ AddCommGrpCat.{u + 1}).mapShortComplex.obj C).Exact)

end AlgebraicGeometry.AlgebraicSpace.GeometricPoint
