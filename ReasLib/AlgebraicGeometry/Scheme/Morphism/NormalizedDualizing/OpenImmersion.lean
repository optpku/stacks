module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.NormalizedDualizing.Relative
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex.RelativeTo

/-- Relative normalized dualizing complexes on finite-type schemes are compatible with derived
pullback along open immersions. -/
theorem isIsomorphic_pullback_of_isOpenImmersion
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : Scheme.FiniteTypeOver S} (j : X ⟶ Y) [IsOpenImmersion j.hom.left] :
    let X' : Scheme := X.obj.left
    let Y' : Scheme := Y.obj.left
    let j' : X' ⟶ Y' := j.hom.left
    ∀ [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
      (HS : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace))
      [MonoidalCategory (RingedSpace.ModuleDerived X'.toRingedSpace)]
      (HX : MonoidalClosed (RingedSpace.ModuleDerived X'.toRingedSpace))
      [MonoidalCategory (RingedSpace.ModuleDerived Y'.toRingedSpace)]
      (HY : MonoidalClosed (RingedSpace.ModuleDerived Y'.toRingedSpace))
      (ωS : RingedSpace.ModuleDerived S.toRingedSpace) (hωS : ωS.IsDualizingComplex HS)
      (ωX : RingedSpace.ModuleDerived X'.toRingedSpace)
      (ωY : RingedSpace.ModuleDerived Y'.toRingedSpace)
      (hX : @RelativeTo _ _ _ X.obj.hom (Scheme.FiniteTypeOver.instFiniteType X)
        _ HS _ HX ωS hωS ωX)
      (hY : @RelativeTo _ _ _ Y.obj.hom (Scheme.FiniteTypeOver.instFiniteType Y)
        _ HS _ HY ωS hωS ωY),
      IsIsomorphic ωX ((RingedSpace.modulePullbackDerived j'.toShHom).obj ωY) := sorry

end AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex.RelativeTo
