/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Sections
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.ProRealization
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.EssentialImage

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- The pro-quasicoherent module on `S.X` represented by the inverse system
`n ↦ (H⁰(S.U, Fₙ))̃`. -/
noncomputable def sectionsProObject (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) : Pro (QCoh S.X) :=
  (Pro.lim.{u + 1, u, 0, 0} ℕᵒᵖ).obj
    (sectionsSystem S F ⋙
      (AlgebraicGeometry.tildeEquiv (R := CommRingCat.of A)).functor)

/-- The defining presentation of `sectionsProObject S F`. -/
theorem sectionsProObject_eq (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) :
    sectionsProObject S F =
      (Pro.lim.{u + 1, u, 0, 0} ℕᵒᵖ).obj
        (sectionsSystem S F ⋙
          (AlgebraicGeometry.tildeEquiv (R := CommRingCat.of A)).functor) := sorry

/-- The predicate that the pro-object of associated global-section sheaves comes from a
coherent formal module on the ambient affine scheme. -/
def CanonicallyExtends (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) : Prop :=
  (proFunctor (idealSheafDataOfIdealOnSpec S.I)).essImage
    (sectionsProObject S F)

/-- A canonical extension is equivalent to the existence of a coherent formal module whose
pro-realization is isomorphic to the associated global-section pro-object. -/
theorem canonicallyExtends_iff (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) :
    CanonicallyExtends S F ↔
      ∃ G : CoherentFormalModules S.X (idealSheafDataOfIdealOnSpec S.I),
        Nonempty ((proFunctor (idealSheafDataOfIdealOnSpec S.I)).obj G ≅
          sectionsProObject S F) := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
