module

public import ReasLib.Algebra.Category.GradedModuleCat.IdealPowerTorsion
public import ReasLib.RingTheory.AdicCompletion.GradedQuotient
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.CanonicalExtension
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Algebraization.ModuleSystem
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Restriction

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AffineAlgebraizationSetup.Graded

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable {𝒜 : ℕ → Submodule ℤ A} [GradedAlgebra 𝒜]

/-- The inverse system of restricted associated sheaves of a graded module system. -/
def restrictedTildeSystem (S : AffineAlgebraizationSetup A)
    (M : SequentialInverseSystem (GradedModuleCat 𝒜)) :
    SequentialInverseSystem S.U.toScheme.Modules :=
  M ⋙ GradedModuleCat.forget ⋙ tilde.functor (CommRingCat.of A) ⋙
    Scheme.Modules.restrictFunctor S.U.ι

/-- Each stage of the restricted associated-sheaf system is the restriction of the tilde module. -/
theorem restrictedTildeSystem_obj (S : AffineAlgebraizationSetup A)
    (M : SequentialInverseSystem (GradedModuleCat 𝒜)) (n : ℕ) :
    (restrictedTildeSystem S M).obj (op n) =
      (Scheme.Modules.restrictFunctor S.U.ι).obj
        ((tilde.functor (CommRingCat.of A)).obj (M.obj (op n)).module) := sorry

/-- A graded system realizes a coherent formal module if their restricted associated-sheaf
systems are isomorphic, compatibly with the transition maps. -/
def Realizes (S : AffineAlgebraizationSetup A)
    (F : Scheme.CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (M : SequentialInverseSystem (GradedModuleCat 𝒜)) : Prop :=
  Nonempty (restrictedTildeSystem S M ≅
    F.obj ⋙ (SheafOfModules.isCoherent S.U.toScheme.ringCatSheaf).ι)

/-- Realization is equivalent to a transition-compatible isomorphism of the underlying systems. -/
theorem realizes_iff (S : AffineAlgebraizationSetup A)
    (F : Scheme.CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (M : SequentialInverseSystem (GradedModuleCat 𝒜)) :
    Realizes S F M ↔ Nonempty (restrictedTildeSystem S M ≅
      F.obj ⋙ (SheafOfModules.isCoherent S.U.toScheme.ringCatSheaf).ι) := sorry

/-- The coherent module on the affine spectrum associated to a finite graded module. -/
def associatedCoherent (S : AffineAlgebraizationSetup A) (N : GradedModuleCat.FG 𝒜) :
    RingedSpace.Coh S.X.toRingedSpace :=
  coherentTildeFunctor.obj ⟨N.obj.module, N.property⟩

/-- The underlying sheaf of the associated coherent module is the associated tilde module. -/
theorem associatedCoherent_obj (S : AffineAlgebraizationSetup A) (N : GradedModuleCat.FG 𝒜) :
    (associatedCoherent S N).obj = tildeObject ⟨N.obj.module, N.property⟩ := sorry

/-- A canonically extending coherent formal module realized by a graded system is induced by
one finite graded module, both modulo irrelevant-ideal power torsion and by restricted completion. -/
theorem exists_finite_of_canonicallyExtends
    (S : AffineAlgebraizationSetup A) (I : HomogeneousIdeal 𝒜)
    (h_a : S.a = (HomogeneousIdeal.irrelevant 𝒜).toIdeal) (h_I : S.I = I.toIdeal)
    (F : Scheme.CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (M : SequentialInverseSystem (GradedModuleCat 𝒜))
    (h_realizes : Realizes S F M)
    (h_extends : Scheme.CoherentFormalModules.CanonicallyExtends S F) :
    ∃ N : GradedModuleCat.FG 𝒜,
      Nonempty
        (GradedModuleCat.torsionQuotientPro (HomogeneousIdeal.irrelevant 𝒜).toIdeal
            (AdicCompletion.Graded.idealPowerQuotientSystem I N.obj) ≅
          GradedModuleCat.torsionQuotientPro (HomogeneousIdeal.irrelevant 𝒜).toIdeal M) ∧
      Nonempty
        ((Scheme.coherentFormalModulesRestrictionFunctor
            (Scheme.idealSheafDataOfIdealOnSpec S.I) S.U).obj
            ((Scheme.CoherentCompletion.functor (Scheme.idealSheafDataOfIdealOnSpec S.I)).obj
              (associatedCoherent S N)) ≅ F) := sorry

end AlgebraicGeometry.AffineAlgebraizationSetup.Graded
