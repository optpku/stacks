/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Germ.Morphism.EtaleLocal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Dimension

/-!
# Local fibre dimensions of morphisms of scheme germs

This file defines the local dimension of the fibre of a morphism of scheme
germs and proves that prescribing its value is étale local on source-and-target.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Germ.Hom.Representative

/-- Equivalent neighborhood representatives have the same local fibre dimension at their
distinguished source points. -/
theorem fiberDimensionAt_eq_of_equivalent {X Y : Germ} {f g : Representative X Y}
    (h : Equivalent f g) :
    f.hom.fiberDimensionAt (X.pointIn f.neighborhood f.mem_neighborhood) =
      g.hom.fiberDimensionAt (X.pointIn g.neighborhood g.mem_neighborhood) := sorry

end AlgebraicGeometry.Scheme.Germ.Hom.Representative

namespace AlgebraicGeometry.Scheme.Germ.Hom

/-- The local dimension of the fibre of a morphism of scheme germs at its distinguished
source point. -/
noncomputable def fiberDimensionAt {X Y : Germ} (f : X ⟶ Y) : WithBot ℕ∞ :=
  let r : Representative X Y := Quotient.out f
  r.hom.fiberDimensionAt (X.pointIn r.neighborhood r.mem_neighborhood)

/-- The local fibre dimension of a represented germ morphism is computed on its
representative. -/
theorem fiberDimensionAt_mk {X Y : Germ} (r : Representative X Y) :
    fiberDimensionAt (mk r) =
      r.hom.fiberDimensionAt (X.pointIn r.neighborhood r.mem_neighborhood) := sorry

end AlgebraicGeometry.Scheme.Germ.Hom

namespace AlgebraicGeometry.Scheme.Germ.MorphismProperty

/-- The property that a morphism of scheme germs has local fibre dimension `d`. -/
noncomputable def fiberDimensionEq (d : ℕ∞) : CategoryTheory.MorphismProperty Germ :=
  fun {_ _} f ↦ Hom.fiberDimensionAt f = (d : WithBot ℕ∞)

/-- A germ morphism satisfies `fiberDimensionEq d` exactly when its local fibre dimension is
`d`. -/
theorem fiberDimensionEq_iff {X Y : Germ} (d : ℕ∞) (f : X ⟶ Y) :
    fiberDimensionEq d f ↔ Hom.fiberDimensionAt f = (d : WithBot ℕ∞) := sorry

/-- For each `d : ℕ∞`, having local fibre dimension `d` is étale local on the
source-and-target for morphisms of scheme germs. -/
theorem fiberDimensionEq_isEtaleLocal (d : ℕ∞) :
    IsEtaleLocal (fiberDimensionEq d) := sorry

end AlgebraicGeometry.Scheme.Germ.MorphismProperty
