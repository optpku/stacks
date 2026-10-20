/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.CanonicalExtension
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Inequalities
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Local
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Restriction
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Intrinsic
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension
public import ReasLib.RingTheory.Depth

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/-- Over a Noetherian ring admitting a dualizing complex, a coherent formal module
along an ideal of local cohomological dimension one extends canonically when it is
pro-isomorphic to a coherent inverse system with weighted stalk depth at least three
at every point of the closed fiber in the open complement. -/
theorem canonicallyExtends_of_proDepth
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (S : AffineAlgebraizationSetup A)
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A), CategoryTheory.DerivedCategory.IsDualizing K)
    (h_cd :
      Ideal.LocalCohomology.dimension S.I S.I.fg_of_isNoetherianRing = 1)
    (F : CoherentFormalModules S.U.toScheme
      ((idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (h_pro :
      ∃ G : SequentialInverseSystem
          (RingedSpace.Coh ((S.U.toScheme).toRingedSpace)),
        Nonempty
            ((Pro.lim.{u + 1, u, 0, 0} ℕᵒᵖ).obj F.obj ≅
              (Pro.lim.{u + 1, u, 0, 0} ℕᵒᵖ).obj G) ∧
          ∀ (n : ℕ) (y : S.Y),
            (hy : S.y y ∈ S.U) →
              (3 : ℕ∞) ≤
                moduleDepth ((S.U.toScheme).presheaf.stalk
                  (closedFiberOpenPoint S y hy))
                  (RingedSpace.stalkModuleCat
                    ((G.obj (op n)).obj)
                    (closedFiberOpenPoint S y hy)) +
                  algebraizationDistance S y) :
    CanonicallyExtends S F := sorry

/-- Over a Noetherian ring admitting a dualizing complex, a coherent formal module
on the open complement satisfying the ordinary `(2, 3)` inequalities extends to the
affine scheme when the defining ideal has local cohomological dimension one. -/
theorem extends_of_cohomologicalDimension_one
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (S : AffineAlgebraizationSetup A)
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A), CategoryTheory.DerivedCategory.IsDualizing K)
    (h_cd :
      Ideal.LocalCohomology.dimension S.I S.I.fg_of_isNoetherianRing = 1)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (h_ineq : SatisfiesInequalities S F 2 3) :
    extendsTo (Scheme.idealSheafDataOfIdealOnSpec S.I) S.U F := sorry

/-- Over an adically complete Noetherian ring admitting a dualizing complex, a
coherent formal module on the open complement satisfying the ordinary `(2, 3)`
inequalities is the completion of a coherent module when the defining ideal has
local cohomological dimension one. -/
theorem isCompletion_of_cohomologicalDimension_one
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (S : AffineAlgebraizationSetup A) [IsAdicComplete S.I A]
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A), CategoryTheory.DerivedCategory.IsDualizing K)
    (h_cd :
      Ideal.LocalCohomology.dimension S.I S.I.fg_of_isNoetherianRing = 1)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (h_ineq : SatisfiesInequalities S F 2 3) :
    (Scheme.CoherentCompletion.functor
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)).essImage F := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
