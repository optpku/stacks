module

public import Mathlib.AlgebraicGeometry.Over
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Point
public import stacks_project.Chap57.Definition_57_15_1_Kernel

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
  isRelative : FourierMukaiObject.IsRelativeEquivalenceKernel kernel

namespace FourierMukaiObject.RelativeEquivalenceFamily

/-- Pack a finite-type base, two smooth proper morphisms, and a relative
equivalence kernel into a relative equivalence family. -/
def ofObjects {K : Type u} [Field K]
    (base : SchemeOverField K) (finiteType : Scheme.Hom.FiniteType base.hom)
    (X Y : FourierMukaiObject base.left)
    (kernel : @RingedSpace.ModuleDerived.Perfect
      (Limits.pullback X.hom Y.hom).toRingedSpace)
    (isRelative : FourierMukaiObject.IsRelativeEquivalenceKernel kernel) :
    RelativeEquivalenceFamily K where
  base := base
  finiteType := finiteType
  X := X
  Y := Y
  kernel := kernel
  isRelative := isRelative

/-- The `K`-fiber of the first family member along a `K`-point of the base. -/
noncomputable def fiberX {K : Type u} [Field K]
    (F : RelativeEquivalenceFamily K) (s : SchemeOverField.point K ⟶ F.base) :
    SchemeOverField K :=
  (Over.map (SchemeOverField.point K).hom).obj
    ((Over.pullback s.left).obj (Over.mk F.X.hom))

/-- The `K`-fiber of the second family member along a `K`-point of the base. -/
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
      FourierMukaiObject.IsRelativeEquivalenceKernel F.kernel := sorry

end FourierMukaiObject.RelativeEquivalenceFamily
