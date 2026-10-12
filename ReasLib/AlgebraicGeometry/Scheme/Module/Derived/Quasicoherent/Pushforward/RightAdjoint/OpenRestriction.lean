/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.OpenRestriction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.BaseChange.RightAdjoint
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.RightAdjoint.Support

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

namespace BaseChange

/-- For a perfect proper morphism of Noetherian schemes, the canonical right-adjoint mate
associated to restriction along an open subscheme is an isomorphism. -/
theorem rightMate_isIso_of_perfect_proper_open_restriction
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsProper f] [LocallyOfType RingHom.IsPerfectRingMap f]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X)
    (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (V : Y.Opens)
    (aV : DerivedQCoh V.toScheme ⥤ DerivedQCoh (f ⁻¹ᵁ V).toScheme)
    (aVAdjunction : pushforwardCohomologyIn (f ∣_ V) ⊣ aV) :
    IsIso
      (rightMate (f ⁻¹ᵁ V).ι (f ∣_ V) f V.ι
        (isPullback_morphismRestrict f V).flip.toCommSq
        a aV aAdjunction aVAdjunction) := sorry

end BaseChange

/-- For a perfect proper morphism of Noetherian schemes, the canonical comparison between
restriction after its derived quasicoherent right adjoint and the local right adjoint after
restriction is an isomorphism on every object. -/
theorem rightAdjoint_openRestrictionComparison_isIso_of_perfect_proper
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsProper f] [LocallyOfType RingHom.IsPerfectRingMap f]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X)
    (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (V : Y.Opens)
    (aV : DerivedQCoh V.toScheme ⥤ DerivedQCoh (f ⁻¹ᵁ V).toScheme)
    (aVAdjunction : pushforwardCohomologyIn (f ∣_ V) ⊣ aV)
    (K : DerivedQCoh Y) :
    IsIso
      ((DerivedBaseChange.mapOfRight
        (pullbackPushforwardAdjunction V.ι)
        (pullbackPushforwardAdjunction (f ⁻¹ᵁ V).ι)
        (@asIso _ _ _ _
          (BaseChange.rightMate
            (f ⁻¹ᵁ V).ι (f ∣_ V) f V.ι
            (isPullback_morphismRestrict f V).flip.toCommSq
            a aV aAdjunction aVAdjunction)
          (BaseChange.rightMate_isIso_of_perfect_proper_open_restriction
            f a aAdjunction V aV aVAdjunction)).inv).app K) := sorry

/-- For a proper, flat morphism of finite presentation over a quasi-compact quasi-separated
scheme, the canonical comparison between restriction after its derived quasicoherent right
adjoint and the local right adjoint after restriction is an isomorphism on every object. -/
theorem rightAdjoint_openRestrictionComparison_isIso_of_proper_flat
    {X Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X)
    (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (V : Y.Opens) [CompactSpace V]
    (aV : DerivedQCoh V.toScheme ⥤ DerivedQCoh (f ⁻¹ᵁ V).toScheme)
    (aVAdjunction : pushforwardCohomologyIn (f ∣_ V) ⊣ aV)
    (K : DerivedQCoh Y) :
    IsIso
      ((DerivedBaseChange.mapOfRight
        (@pullbackPushforwardAdjunction _ _ V.ι
          (inferInstance : QuasiCompact V.ι)
          (inferInstance : QuasiSeparated V.ι))
        (@pullbackPushforwardAdjunction _ _ (f ⁻¹ᵁ V).ι
          (Scheme.Hom.inverseImageOpenιQuasiCompact f V)
          (inferInstance : QuasiSeparated (f ⁻¹ᵁ V).ι))
        (@asIso _ _ _ _
          (@BaseChange.rightMate
            (f ⁻¹ᵁ V).toScheme X V.toScheme Y
            (f ⁻¹ᵁ V).ι (f ∣_ V) f V.ι
            (inferInstance : QuasiCompact f)
            (inferInstance : QuasiSeparated f)
            (inferInstance : QuasiCompact (f ∣_ V))
            (inferInstance : QuasiSeparated (f ∣_ V))
            (inferInstance : QuasiCompact V.ι)
            (inferInstance : QuasiSeparated V.ι)
            (Scheme.Hom.inverseImageOpenιQuasiCompact f V)
            (inferInstance : QuasiSeparated (f ⁻¹ᵁ V).ι)
            (isPullback_morphismRestrict f V).flip.toCommSq
            a aV aAdjunction aVAdjunction)
          (@BaseChange.rightMate_isIso_of_flat
            (f ⁻¹ᵁ V).toScheme X V.toScheme Y
            (Scheme.Hom.inverseImageOpenCompactSpace f V)
            (Scheme.Hom.inverseImageOpenQuasiSeparatedSpace f V)
            (Scheme.Hom.compactSpace_of_finitePresentation f)
            (Scheme.Hom.quasiSeparatedSpace_of_finitePresentation f)
            (inferInstance : CompactSpace V) (Scheme.openQuasiSeparatedSpace V)
            (inferInstance : CompactSpace Y) (inferInstance : QuasiSeparatedSpace Y)
            (f ⁻¹ᵁ V).ι (f ∣_ V) f V.ι (inferInstance : Flat V.ι)
            (isPullback_morphismRestrict f V).flip
            a aV aAdjunction aVAdjunction)).inv).app K) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
