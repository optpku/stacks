/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.SmallEtalePoint

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

@[expose] public section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GeometricPoint

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- A morphism of set-valued sheaves on the small étale site of an algebraic space is
a monomorphism if and only if its map on every geometric stalk is injective. -/
theorem sheafTypeMap_mono_iff_stalk {F G : Sheaf (smallEtaleTopology X) (Type (u + 1))}
    (a : F ⟶ G) :
    Mono a ↔ ∀ xbar : GeometricPoint X,
      Function.Injective
        (ConcreteCategory.hom ((toSmallEtalePoint xbar).sheafFiber.map a)) :=
  sorry

/-- A morphism of set-valued sheaves on the small étale site of an algebraic space is
an epimorphism if and only if its map on every geometric stalk is surjective. -/
theorem sheafTypeMap_epi_iff_stalk {F G : Sheaf (smallEtaleTopology X) (Type (u + 1))}
    (a : F ⟶ G) :
    Epi a ↔ ∀ xbar : GeometricPoint X,
      Function.Surjective
        (ConcreteCategory.hom ((toSmallEtalePoint xbar).sheafFiber.map a)) :=
  sorry

/-- A short complex of abelian sheaves on the small étale site of an algebraic space is
exact if and only if its image on every geometric stalk is exact. -/
theorem sheafAbelian_exact_iff_stalk
    (C : ShortComplex (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})) :
    C.Exact ↔ ∀ xbar : GeometricPoint X,
      (((toSmallEtalePoint xbar).sheafFiber :
          _ ⥤ AddCommGrpCat.{u + 1}).mapShortComplex.obj C).Exact :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.GeometricPoint
