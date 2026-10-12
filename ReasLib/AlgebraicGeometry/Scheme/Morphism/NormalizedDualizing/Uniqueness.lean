/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.NormalizedDualizing

@[expose] public section

open CategoryTheory AlgebraicGeometry.Scheme.Hom

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Hom
namespace NormalizedDualizingComplexOnCover

/-- An isomorphism between normalized dualizing complexes on a fixed cover is compatible when
its restriction intertwines every chosen local normalization isomorphism. -/
abbrev IsCompatibleIso {S X : Scheme.{u}} [IsNoetherian S]
    {f : X ⟶ S} [FiniteType f]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    {HS : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    {HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)}
    {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex HS}
    {cover : FiniteSeparatedOpenCover f} {duality : ExceptionalInverseImageSetup f cover}
    (K K' : NormalizedDualizingComplexOnCover f HS HX ωS hωS cover duality)
    (e : K.complex ≅ K'.complex) : Prop :=
  ∀ i : cover.index,
    (RingedSpace.moduleRestrictionToOpenDerived X.toRingedSpace
        (cover.opens i)).mapIso e ≪≫ K'.normalizationIso i = K.normalizationIso i

/-- A compatible isomorphism intertwines the normalization on each chosen open. -/
theorem IsCompatibleIso.w {S X : Scheme.{u}} [IsNoetherian S]
    {f : X ⟶ S} [FiniteType f]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    {HS : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    {HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)}
    {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex HS}
    {cover : FiniteSeparatedOpenCover f} {duality : ExceptionalInverseImageSetup f cover}
    {K K' : NormalizedDualizingComplexOnCover f HS HX ωS hωS cover duality}
    {e : K.complex ≅ K'.complex} (h : IsCompatibleIso K K' e) (i : cover.index) :
    (RingedSpace.moduleRestrictionToOpenDerived X.toRingedSpace
        (cover.opens i)).mapIso e ≪≫ K'.normalizationIso i = K.normalizationIso i := sorry

/-- Two normalized dualizing complexes on the same finite separated cover are uniquely
isomorphic compatibly with every local normalization. -/
theorem existsUniqueIso {S X : Scheme.{u}} [IsNoetherian S]
    (f : X ⟶ S) [FiniteType f]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    (HS : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace))
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (ωS : RingedSpace.ModuleDerived S.toRingedSpace) (hωS : ωS.IsDualizingComplex HS)
    (cover : FiniteSeparatedOpenCover f) (duality : ExceptionalInverseImageSetup f cover)
    (K K' : NormalizedDualizingComplexOnCover f HS HX ωS hωS cover duality) :
    ∃! e : K.complex ≅ K'.complex, IsCompatibleIso K K' e := sorry

end NormalizedDualizingComplexOnCover
end Hom
end Scheme
end AlgebraicGeometry
