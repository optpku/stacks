/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.Frobenius
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 51.19.5: if `p` is prime and vanishes in `A`, and
`f : V ⟶ Spec (CommRingCat.of A)` is quasi-compact, quasi-separated, and étale, then derived
global sections of `𝒪_V` are invariant under derived extension of scalars along Frobenius. -/
@[stacks 0EC9] #check
  (AlgebraicGeometry.Scheme.Modules.etaleStructureSheaf_frobeniusBaseChangeIso :
    ∀ {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime] (hp : (p : A) = 0)
      {V : Scheme.{u}} (f : V ⟶ Spec (CommRingCat.of A))
      [QuasiCompact f] [QuasiSeparated f] [Etale f]
      [AffineBaseModuleDerivedAdjunction.HasRightDerived A f],
    Nonempty
      ((ModuleCat.derivedExtensionOfScalars (RingHom.frobeniusOfPrime p hp)).obj
          (affineBaseModuleDerivedGlobalSections A f
            (SheafOfModules.unit V.ringCatSheaf)) ≅
        affineBaseModuleDerivedGlobalSections A f
          (SheafOfModules.unit V.ringCatSheaf)))

end AlgebraicGeometry.Scheme.Modules
