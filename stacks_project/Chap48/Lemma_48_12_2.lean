/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.RightAdjoint.OpenRestriction
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Lemma 48.12.2 (1): if `f : X ⟶ Y` is proper, flat, and of finite presentation over
a quasi-compact and quasi-separated scheme, then a right adjoint `a` to `pushforward f`
sends objects supported on a closed subset `T` to objects supported on its inverse image. -/
@[stacks 0E4J]
#check (AlgebraicGeometry.Scheme.DerivedQCoh.rightAdjoint_isSupportedOn_preimage_of_proper_flat :
  ∀ {X Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X)
    (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (T : TopologicalSpace.Closeds Y) (Q : DerivedQCoh Y),
    RingedSpace.ModuleDerived.IsSupportedOn Q.obj (T : Set Y) →
      RingedSpace.ModuleDerived.IsSupportedOn
        (a.obj Q).obj (T.preimage f.continuous : Set X))

/- Lemma 48.12.2 (2): for every quasi-compact open `V ⊆ Y` and `K : DerivedQCoh Y`,
the open-restriction comparison (48.4.1.1) for a right adjoint `a` to `pushforward f`
is an isomorphism when `f` is proper, flat, and of finite presentation. -/
@[stacks 0E4J]
#check (AlgebraicGeometry.Scheme.DerivedQCoh.rightAdjoint_openRestrictionComparison_isIso_of_proper_flat :
  ∀ {X Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X)
    (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (V : Y.Opens) [CompactSpace V]
    (aV : DerivedQCoh V.toScheme ⥤ DerivedQCoh (f ⁻¹ᵁ V).toScheme)
    (aVAdjunction : pushforwardCohomologyIn (f ∣_ V) ⊣ aV)
    (K : DerivedQCoh Y),
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
            a aV aAdjunction aVAdjunction)).inv).app K))

end AlgebraicGeometry.Scheme.DerivedQCoh
