module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.NormalizedDualizing.Relative

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

#check (AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex.RelativeTo :
  ∀ {S X : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [Scheme.Hom.FiniteType f]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    (HS : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace))
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (ωS : RingedSpace.ModuleDerived S.toRingedSpace) (hωS : ωS.IsDualizingComplex HS)
    (ωX : RingedSpace.ModuleDerived X.toRingedSpace), Prop)

#check (AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex.relativeTo_iff_exists_onCover :
  ∀ {S X : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [Scheme.Hom.FiniteType f]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    (HS : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace))
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (ωS : RingedSpace.ModuleDerived S.toRingedSpace) (hωS : ωS.IsDualizingComplex HS)
    (ωX : RingedSpace.ModuleDerived X.toRingedSpace),
    AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex.RelativeTo
        f HS HX ωS hωS ωX ↔
      ∃ cover : Scheme.Hom.FiniteSeparatedOpenCover f,
        ∃ duality : Scheme.Hom.ExceptionalInverseImageSetup f cover,
          ∃ K : Scheme.Hom.NormalizedDualizingComplexOnCover f HS HX ωS hωS cover duality,
            K.complex = ωX)

#check (AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex.RelativeTo.ofOnCover :
  ∀ {S X : Scheme.{u}} [IsNoetherian S] {f : X ⟶ S} [Scheme.Hom.FiniteType f]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    {HS : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    {HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)}
    {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex HS}
    {cover : Scheme.Hom.FiniteSeparatedOpenCover f}
    {duality : Scheme.Hom.ExceptionalInverseImageSetup f cover}
    (K : Scheme.Hom.NormalizedDualizingComplexOnCover f HS HX ωS hωS cover duality),
    AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex.RelativeTo
      f HS HX ωS hωS K.complex)

#check (AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex.RelativeTo.isDualizing :
  ∀ {S X : Scheme.{u}} [IsNoetherian S] {f : X ⟶ S} [Scheme.Hom.FiniteType f]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    {HS : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    {HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)}
    {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex HS}
    {ωX : RingedSpace.ModuleDerived X.toRingedSpace}
    (hωX : AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex.RelativeTo
      f HS HX ωS hωS ωX),
    ωX.IsDualizingComplex HX)
