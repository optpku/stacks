/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.AffineAlgebraization
public import ReasLib.AlgebraicGeometry.Scheme.AffineAlgebraization.Completion
public import ReasLib.AlgebraicGeometry.Scheme.Noetherian.Open
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.AdicCompletion.Basic

@[expose] public section
open CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme AlgebraicGeometry.RingedSpace
universe u
namespace AlgebraicGeometry.AffineAlgebraizationSetup
variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- For a coherent formal module on the open complement, completion on the open,
completion on a neighborhood of the support, completion after restriction, and
restriction after completion form five equivalent conditions. -/
theorem algebraization_tfae (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) :
    let U := S.U.toScheme
    let IX := idealSheafDataOfIdealOnSpec S.I
    let IU := IX.comap S.U.ι
    let c₁ := (CoherentCompletion.functor IU).essImage F
    let c₂ := ∃ G : Coh U.toRingedSpace,
      Nonempty ((CoherentCompletion.functor IU).obj G ≅ F)
    let c₃ := ∃ V : TopologicalSpace.Opens S.U,
      (IU.support : Set S.U) ⊆ (V : Set S.U) ∧
        (CoherentCompletion.functor (IU.comap (Scheme.Opens.ι V))).essImage
          ((coherentFormalModulesRestrictionFunctor IU V).obj F)
    let c₄ :=
      (Modules.coherentRestrictFunctor S.U.ι ⋙
        CoherentCompletion.functor IU).essImage F
    let c₅ :=
      (CoherentCompletion.functor IX ⋙
        coherentFormalModulesRestrictionFunctor IX S.U).essImage F
    List.TFAE [c₁, c₂, c₃, c₄, c₅] := sorry

/-- The restriction of a completion on the ambient affine scheme extends to a
coherent formal module on that scheme. -/
theorem extends_of_globalCompletion (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) :
    let IX := idealSheafDataOfIdealOnSpec S.I
    (CoherentCompletion.functor IX ⋙
      coherentFormalModulesRestrictionFunctor IX S.U).essImage F →
        (coherentFormalModulesRestrictionFunctor IX S.U).essImage F := sorry

/-- If the ring is complete along the distinguished ideal, a coherent formal
module on the open complement that extends to the ambient scheme is obtained by
completion and restriction from that scheme. -/
theorem globalCompletion_of_extends (S : AffineAlgebraizationSetup A)
    [IsAdicComplete S.I A]
    (F : CoherentFormalModules S.U.toScheme
      ((idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) :
    let IX := idealSheafDataOfIdealOnSpec S.I
    (coherentFormalModulesRestrictionFunctor IX S.U).essImage F →
      (CoherentCompletion.functor IX ⋙
        coherentFormalModulesRestrictionFunctor IX S.U).essImage F := sorry

/-- Extension to the ambient affine scheme is equivalent to completion after pullback to the
punctured spectrum of the adic completion. -/
theorem extends_iff_completion_after_adicPullback (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (pullback : CoherentFormalModules S.U.toScheme
        ((idealSheafDataOfIdealOnSpec S.I).comap S.U.ι) ⥤
      CoherentFormalModules S.completionOpen.toScheme S.completionIdealOnOpen)
    (h_pullback : IsCoherentFormalModulesPullbackFunctor S.completionOpenMap
      ((idealSheafDataOfIdealOnSpec S.I).comap S.U.ι) pullback) :
    (coherentFormalModulesRestrictionFunctor
      (idealSheafDataOfIdealOnSpec S.I) S.U).essImage F ↔
      (CoherentCompletion.functor S.completionIdealOnOpen).essImage
        (pullback.obj F) := sorry

end AlgebraicGeometry.AffineAlgebraizationSetup
