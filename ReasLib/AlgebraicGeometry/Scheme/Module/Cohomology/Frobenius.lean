module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.DerivedBaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Etale

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- If `p` is prime and vanishes in `A`, derived global sections of the structure sheaf
on a quasi-compact, quasi-separated étale scheme over `Spec (CommRingCat.of A)` are
invariant under derived extension of scalars along Frobenius. -/
theorem etaleStructureSheaf_frobeniusBaseChangeIso
    {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime] (hp : (p : A) = 0)
    {V : Scheme.{u}} (f : V ⟶ Spec (CommRingCat.of A))
    [QuasiCompact f] [QuasiSeparated f] [Etale f]
    [AffineBaseModuleDerivedAdjunction.HasRightDerived A f] :
    Nonempty
      ((ModuleCat.derivedExtensionOfScalars (RingHom.frobeniusOfPrime p hp)).obj
          (affineBaseModuleDerivedGlobalSections A f
            (SheafOfModules.unit V.ringCatSheaf)) ≅
        affineBaseModuleDerivedGlobalSections A f
          (SheafOfModules.unit V.ringCatSheaf)) := sorry

end AlgebraicGeometry.Scheme.Modules
