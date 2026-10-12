/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Germ.Morphism.EtaleLocal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Dimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Stalk

/-!
# Fibre-stalk Krull dimension of morphisms of scheme germs

This file defines the property that the local ring of the fibre at the
distinguished source point has a prescribed Krull dimension and records its
invariance under étale localization on source and target.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Germ.MorphismProperty

/-- A morphism of scheme germs has fibre-stalk Krull dimension `d` if this holds for
one representative at its distinguished source point. -/
def fiberStalkKrullDimEq (d : ℕ∞) : CategoryTheory.MorphismProperty Germ :=
  fun {X Y} f ↦
    ∃ r : Hom.Representative X Y,
      Hom.mk r = f ∧
        ringKrullDim
            (Scheme.Hom.fiberStalkAt r.hom
              (X.pointIn r.neighborhood r.mem_neighborhood)) =
          (d : WithBot ℕ∞)

/-- A represented germ morphism has fibre-stalk Krull dimension `d` exactly when its
given representative has that fibre-stalk Krull dimension. -/
theorem fiberStalkKrullDimEq_mk_iff {X Y : Germ} (d : ℕ∞)
    (r : Hom.Representative X Y) :
    fiberStalkKrullDimEq d (Hom.mk r) ↔
      ringKrullDim
          (Scheme.Hom.fiberStalkAt r.hom
            (X.pointIn r.neighborhood r.mem_neighborhood)) =
        (d : WithBot ℕ∞) := sorry

/-- Having a prescribed fibre-stalk Krull dimension is étale local on the source
and target for morphisms of scheme germs. -/
theorem fiberStalkKrullDimEq_isEtaleLocal (d : ℕ∞) :
    IsEtaleLocal (fiberStalkKrullDimEq d) := sorry

end AlgebraicGeometry.Scheme.Germ.MorphismProperty
