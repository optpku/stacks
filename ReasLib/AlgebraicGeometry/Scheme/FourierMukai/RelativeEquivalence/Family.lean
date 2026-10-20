module

public import Mathlib.AlgebraicGeometry.Over
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Point
public import ReasLib.AlgebraicGeometry.Scheme.FourierMukai.RelativeEquivalence

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- A finite-type `K`-scheme equipped with two smooth proper morphisms and a
perfect Fourier--Mukai kernel of a relative equivalence between them. -/
structure FourierMukaiObject.RelativeEquivalenceFamily (K : Type u) [Field K] where
  base : SchemeOverField K
  finiteType : Scheme.Hom.FiniteType base.hom
  X : FourierMukaiObject base.left
  Y : FourierMukaiObject base.left
  kernel : @RingedSpace.ModuleDerived.Perfect
    (Limits.pullback X.hom Y.hom).toRingedSpace
  isRelative : IsIso (C := FourierMukaiObject base.left) (Quotient.mk'' kernel : X ⟶ Y)

/-- The relative identity equivalence family of a finite-type smooth proper object:
the base is a fixed scheme of finite type over `K` and both the source and the target
are the given smooth proper object, equipped with the canonical perfect diagonal kernel. -/
noncomputable def FourierMukaiObject.RelativeEquivalenceFamily.identity {K : Type u} [Field K]
    (base : SchemeOverField K) (finiteType : Scheme.Hom.FiniteType base.hom)
    (X : FourierMukaiObject base.left) : FourierMukaiObject.RelativeEquivalenceFamily K := {
  base := base
  finiteType := finiteType
  X := X
  Y := X
  kernel := FourierMukaiObject.diagonalKernel X
  isRelative := by
    change IsIso (𝟙 X)
    infer_instance }

namespace FourierMukaiObject.RelativeEquivalenceFamily

/-- The `K`-fiber of the first smooth proper scheme along a `K`-point of the base. -/
noncomputable def fiberX {K : Type u} [Field K]
    (F : RelativeEquivalenceFamily K) (s : SchemeOverField.point K ⟶ F.base) :
    SchemeOverField K :=
  (Over.map (SchemeOverField.point K).hom).obj
    ((Over.pullback s.left).obj (Over.mk F.X.hom))

/-- The `K`-fiber of the second smooth proper scheme along a `K`-point of the base. -/
noncomputable def fiberY {K : Type u} [Field K]
    (F : RelativeEquivalenceFamily K) (s : SchemeOverField.point K ⟶ F.base) :
    SchemeOverField K :=
  (Over.map (SchemeOverField.point K).hom).obj
    ((Over.pullback s.left).obj (Over.mk F.Y.hom))

/-- The first fiber is the pullback of the first family morphism, transported
along the structure map of `SchemeOverField.point K`. -/
theorem fiberX_spec {K : Type u} [Field K]
    (F : RelativeEquivalenceFamily K) (s : SchemeOverField.point K ⟶ F.base) :
    F.fiberX s =
      (Over.map (SchemeOverField.point K).hom).obj
        ((Over.pullback s.left).obj (Over.mk F.X.hom)) := sorry

/-- The second fiber is the pullback of the second family morphism, transported
along the structure map of `SchemeOverField.point K`. -/
theorem fiberY_spec {K : Type u} [Field K]
    (F : RelativeEquivalenceFamily K) (s : SchemeOverField.point K ⟶ F.base) :
    F.fiberY s =
      (Over.map (SchemeOverField.point K).hom).obj
        ((Over.pullback s.left).obj (Over.mk F.Y.hom)) := sorry

/-- A relative equivalence family consists of a finite-type base, two smooth
proper morphisms, and a Fourier--Mukai kernel of a relative equivalence. -/
theorem spec {K : Type u} [Field K] (F : RelativeEquivalenceFamily K) :
    Scheme.Hom.FiniteType F.base.hom ∧
      Smooth F.X.hom ∧ IsProper F.X.hom ∧
      Smooth F.Y.hom ∧ IsProper F.Y.hom ∧
      IsIso (C := FourierMukaiObject F.base.left) (Quotient.mk'' F.kernel : F.X ⟶ F.Y) := sorry

end FourierMukaiObject.RelativeEquivalenceFamily
