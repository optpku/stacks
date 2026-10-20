module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiAffine.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Power
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective

/-!
# Quasi-Affineness and Relative Ampleness

This leaf records the structure-sheaf criterion for quasi-affine morphisms and
the resulting quasi-projectivity criterion.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A morphism is quasi-affine exactly when its structure sheaf is relatively ample. -/
theorem quasiAffineHom_iff_structureSheaf_relativelyAmple
    {X S : Scheme.{u}} (f : X ⟶ S) :
    QuasiAffineHom f ↔ RelativelyAmple f (SheafOfModules.unit X.ringCatSheaf) := sorry

/-- A finite-type quasi-affine morphism is quasi-projective. -/
theorem QuasiAffineHom.quasiProjective_of_finiteType
    {X S : Scheme.{u}} {f : X ⟶ S} [Scheme.Hom.FiniteType f]
    (hf : QuasiAffineHom f) :
    QuasiProjective f := sorry

/-- Pullback along a quasi-affine morphism preserves ample invertible modules. -/
theorem Scheme.Modules.isAmpleObject_pullback_of_quasiAffineHom
    {X Y : Scheme.{u}} {f : X ⟶ Y} {M : Y.Modules}
    (hM : Scheme.Modules.isAmpleObject M) (hf : QuasiAffineHom f) :
    Scheme.Modules.isAmpleObject ((Scheme.Modules.pullback f).obj M) := sorry

end AlgebraicGeometry
