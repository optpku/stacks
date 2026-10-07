module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.ExceptionalProjectiveBundle
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.SmoothCenter
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Proper
public import ReasLib.AlgebraicGeometry.Scheme.OverField

/-!
# Blowups over a field

This file records the exceptional projection as a morphism over the base field and the
geometric properties supplied by a smooth center.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.IsBlowup

/-- The exceptional projection of a blowup over a field commutes with the structure maps. -/
theorem exceptionalProjection_comp_structureMap
    {k : Type u} [Field k] {X X' : SchemeOverField k}
    (I : X.left.IdealSheafData) (b : X' ⟶ X) [IsBlowup b.left I] :
    exceptionalProjection I b.left ≫ (I.subschemeι ≫ X.hom) =
      (I.comap b.left).subschemeι ≫ X'.hom := sorry

/-- The exceptional projection of a blowup, regarded as a morphism over the base field. -/
def exceptionalProjectionOver
    {k : Type u} [Field k] {X X' : SchemeOverField k}
    (I : X.left.IdealSheafData) (b : X' ⟶ X) [IsBlowup b.left I] :
    Over.mk ((I.comap b.left).subschemeι ≫ X'.hom) ⟶
      Over.mk (I.subschemeι ≫ X.hom) :=
  Over.homMk (exceptionalProjection I b.left)
    (exceptionalProjection_comp_structureMap I b)

/-- The underlying scheme morphism of the exceptional projection over the field is the
canonical exceptional projection. -/
theorem exceptionalProjectionOver_left
    {k : Type u} [Field k] {X X' : SchemeOverField k}
    (I : X.left.IdealSheafData) (b : X' ⟶ X) [IsBlowup b.left I] :
    (exceptionalProjectionOver I b).left = exceptionalProjection I b.left := sorry

set_option synthInstance.checkSynthOrder false in
/-- The source of a blowup of a smooth scheme in a smooth center is smooth over the
base field. -/
instance sourceSmoothOver
    {k : Type u} [Field k] {X X' : SchemeOverField k} [Smooth X.hom]
    (I : X.left.IdealSheafData) [Smooth (I.subschemeι ≫ X.hom)]
    (b : X' ⟶ X) [IsBlowup b.left I] : Smooth X'.hom := sorry

/-- The exceptional projection of a blowup in a smooth center is proper. -/
instance exceptionalProjectionOver_isProper
    {k : Type u} [Field k] {X X' : SchemeOverField k} [Smooth X.hom]
    (I : X.left.IdealSheafData) [Smooth (I.subschemeι ≫ X.hom)]
    (b : X' ⟶ X) [IsBlowup b.left I] :
    IsProper (exceptionalProjectionOver I b).left := sorry

end AlgebraicGeometry.IsBlowup
