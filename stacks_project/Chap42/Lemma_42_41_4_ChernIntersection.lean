/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.FirstChern.Iterated

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

/- The heterogeneous iterated first-Chern cap operation is provided by its
reusable Chow-group owner. -/
#check (AlgebraicGeometry.ChowGroup.iteratedFirstChernClassCap :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S]
    (delta : S → ℤ) [IsDimensionFunction delta]
    (X : Over S) [LocallyOfFiniteType X.hom] (d : ℕ)
    (L : Fin d → X.left.Modules)
    [∀ j : Fin d, Scheme.Modules.Invertible (L j)],
      @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
          (X.hom.relativeDimensionFunction delta) inferInstance (d : ℤ) →+
        @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
          (X.hom.relativeDimensionFunction delta) inferInstance 0)

/- The empty-family computation law is provided by the reusable Chow-group
owner. -/
#check (AlgebraicGeometry.ChowGroup.iteratedFirstChernClassCap_zero :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S]
    (delta : S → ℤ) [IsDimensionFunction delta]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (L : Fin 0 → X.left.Modules)
    [∀ j : Fin 0, Scheme.Modules.Invertible (L j)],
      AlgebraicGeometry.ChowGroup.iteratedFirstChernClassCap delta X 0 L =
        AddMonoidHom.id
          (@ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
            (X.hom.relativeDimensionFunction delta) inferInstance 0))

/- The successor-family computation law is provided by the reusable
Chow-group owner. -/
#check (AlgebraicGeometry.ChowGroup.iteratedFirstChernClassCap_succ :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S]
    (delta : S → ℤ) [IsDimensionFunction delta]
    (X : Over S) [LocallyOfFiniteType X.hom] (d : ℕ)
    (L : Fin (d + 1) → X.left.Modules)
    [∀ j : Fin (d + 1), Scheme.Modules.Invertible (L j)],
      AlgebraicGeometry.ChowGroup.iteratedFirstChernClassCap delta X (d + 1) L =
        (AlgebraicGeometry.ChowGroup.iteratedFirstChernClassCap
          delta X d (fun j ↦ L j.castSucc)).comp
          ((AddEquiv.cast
            ((congrArg (fun n : ℤ ↦ n - 1) (Nat.cast_succ d)).trans
              (add_sub_cancel_right (d : ℤ) 1)) :
            @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
                (X.hom.relativeDimensionFunction delta) inferInstance
                (((d + 1 : ℕ) : ℤ) - 1) ≃+
              @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
                (X.hom.relativeDimensionFunction delta) inferInstance (d : ℤ)).toAddMonoidHom.comp
            (firstChernClassCap delta X (L (Fin.last d)) ((d + 1 : ℕ) : ℤ))))

end AlgebraicGeometry.ChowGroup
