module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField.PerfectDerived
public import ReasLib.AlgebraicGeometry.Scheme.Regular

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.RingedSpace

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField.PerfectDerived

/-- The degree-zero derived realization of a coherent module on a regular scheme is
perfect. -/
theorem single_isPerfect_of_coherent {k : Type u} [Field k] (X : SchemeOverField k)
    [Scheme.Regular X.left] (ℱ : X.left.Modules) (hℱ : SheafOfModules.IsCoherent ℱ) :
    RingedSpace.ModuleDerived.IsPerfect
      ((DerivedCategory.singleFunctor X.left.Modules (0 : ℤ)).obj ℱ) := sorry

/-- The degree-`0` derived object associated to a coherent `𝒪_X`-module, as an object of
`PerfectDerived X`. -/
def ofCoherentModule {k : Type u} [Field k] (X : SchemeOverField k)
    [Scheme.Regular X.left] (ℱ : X.left.Modules) [SheafOfModules.IsCoherent ℱ] :
    PerfectDerived X :=
  { obj := (DerivedCategory.singleFunctor X.left.Modules (0 : ℤ)).obj ℱ
    property := single_isPerfect_of_coherent X ℱ inferInstance }

/-- The inclusion of the degree-`0` derived object associated to a coherent module. -/
theorem ofCoherentModule_obj {k : Type u} [Field k] (X : SchemeOverField k)
    [Scheme.Regular X.left] (ℱ : X.left.Modules) [SheafOfModules.IsCoherent ℱ] :
    (inclusion X).obj (ofCoherentModule X ℱ) =
      (DerivedCategory.singleFunctor X.left.Modules (0 : ℤ)).obj ℱ := rfl

/-- The degree-zero realization functor from coherent modules on a regular scheme to
its perfect derived category. -/
def coherentFunctor {k : Type u} [Field k] (X : SchemeOverField k)
    [Scheme.Regular X.left] : RingedSpace.Coh X.left.toRingedSpace ⥤ PerfectDerived X where
  obj ℱ :=
    { obj := (DerivedCategory.singleFunctor X.left.Modules (0 : ℤ)).obj ℱ.obj
      property := single_isPerfect_of_coherent X ℱ.obj ℱ.property }
  map f := ObjectProperty.homMk
    ((DerivedCategory.singleFunctor X.left.Modules (0 : ℤ)).map f.hom)
  map_id ℱ := by
    apply ObjectProperty.hom_ext
    exact (DerivedCategory.singleFunctor X.left.Modules (0 : ℤ)).map_id ℱ.obj
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact (DerivedCategory.singleFunctor X.left.Modules (0 : ℤ)).map_comp f.hom g.hom

/-- The degree-zero coherent realization agrees with the coherent-module object
constructor. -/
theorem coherentFunctor_obj {k : Type u} [Field k] (X : SchemeOverField k)
    [Scheme.Regular X.left] (ℱ : X.left.Modules) [SheafOfModules.IsCoherent ℱ] :
    (coherentFunctor X).obj ⟨ℱ, inferInstance⟩ = ofCoherentModule X ℱ := rfl

/-- The underlying map of the coherent realization is the degree-zero derived map. -/
theorem coherentFunctor_map_hom {k : Type u} [Field k] (X : SchemeOverField k)
    [Scheme.Regular X.left] {ℱ 𝒢 : RingedSpace.Coh X.left.toRingedSpace} (f : ℱ ⟶ 𝒢) :
    ((coherentFunctor X).map f).hom =
      (DerivedCategory.singleFunctor X.left.Modules (0 : ℤ)).map f.hom := rfl

end AlgebraicGeometry.SchemeOverField.PerfectDerived

end
