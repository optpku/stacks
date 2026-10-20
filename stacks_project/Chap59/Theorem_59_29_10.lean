/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Stalk.Detection
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

@[expose] public section

universe u

/- Theorem 59.29.10 (1): a map of étale sheaves of sets is injective iff it is
injective on stalks at every geometric point of S. -/
@[stacks 03PU] #check (AlgebraicGeometry.Scheme.Etale.sheafTypeMap_mono_iff_stalk :
  ∀ {S : Scheme.{u}} {F G : Sheaf (smallEtaleTopology S) (Type u)} (a : F ⟶ G),
    Mono a ↔ ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
      Function.Injective
        (ConcreteCategory.hom ((Scheme.pointSmallEtale s).sheafFiber.map a)))

/- Theorem 59.29.10 (2): a map of étale sheaves of sets is surjective iff it is
surjective on stalks at every geometric point of S. -/
@[stacks 03PU] #check (AlgebraicGeometry.Scheme.Etale.sheafTypeMap_epi_iff_stalk :
  ∀ {S : Scheme.{u}} {F G : Sheaf (smallEtaleTopology S) (Type u)} (a : F ⟶ G),
    Epi a ↔ ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
      Function.Surjective
        (ConcreteCategory.hom ((Scheme.pointSmallEtale s).sheafFiber.map a)))

/- Theorem 59.29.10 (3): a sequence of abelian sheaves on S.Etale is exact iff
it is exact on stalks at every geometric point of S. -/
@[stacks 03PU] #check (AlgebraicGeometry.Scheme.Etale.sheafAbelian_exact_iff_stalk :
  ∀ {S : Scheme.{u}} (C : ShortComplex (Sheaf (smallEtaleTopology S) AddCommGrpCat.{u})),
    C.Exact ↔ ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
      (((Scheme.pointSmallEtale s).sheafFiber : _ ⥤ AddCommGrpCat.{u}).mapShortComplex.obj C).Exact)
