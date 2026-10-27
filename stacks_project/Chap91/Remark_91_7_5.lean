/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Solution.Presentation
import StacksCheckRecall

/-!
# Polynomial presentations of square-zero relative ringed-space extensions

For f : X ⟶ S and an 𝒪_X-module 𝒢 as in Lemma 91.7.4, consider an extension
0 ⟶ 𝒢 ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0 of f⁻¹𝒪_S-algebras. Choose a sheaf of sets 𝓔 and
a lift α' : 𝓔 ⟶ 𝒪_{X'} whose reduction is α : 𝓔 ⟶ 𝒪_X, such that polynomial
evaluation f⁻¹𝒪_S[𝓔] ⟶ 𝒪_X is surjective, with kernel 𝒥. Any sheaf of sets
surjecting onto 𝒪_{X'} suffices; its underlying sheaf with the identity lift
gives an explicit choice.

Then NL_{X/S} ≅ NL(α), where NL(α) is the two-term complex
𝒥/𝒥² ⟶ Ω_{f⁻¹𝒪_S[𝓔]/f⁻¹𝒪_S} ⊗_{f⁻¹𝒪_S[𝓔]} 𝒪_X, by Modules, Section 17.31
and Lemma 17.31.2. The canonical comparison goes from this presentation model
to NL_{X/S}; its inverse gives the displayed direction. The lift α' determines
f⁻¹𝒪_S[𝓔] ⟶ 𝒪_{X'}, hence a map 𝒥/𝒥² ⟶ 𝒢. Its class in
Ext¹_{𝒪_X}(NL(α), 𝒢) = Ext¹_{𝒪_X}(NL_{X/S}, 𝒢) is precisely the element
corresponding to the extension under the bijection of Lemma 91.7.4.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Thickening
open AlgebraicGeometry.RingedSpace.Thickening.Solution
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.NaiveCotangent
open TopologicalSpace
open scoped AlgebraicGeometry DerivedExt RingedSpaceDerivedPullback
open scoped CategoryTheory.Sheaf.FreeAlgebra

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening
namespace Solution

variable {S X : RingedSpace.{u}} {f : X ⟶ S} {G : X.Modules}

/- Remark 91.7.5 The conormal map induced by a lifted polynomial presentation
represents the square-zero extension under the canonical Ext¹ classification. -/
@[stacks 0GQ0] #check (AlgebraicGeometry.RingedSpace.Thickening.Solution.extClass_eq_extensionEquiv_symm :
    ∀ (sol : Solution (𝟙 S) f G (zeroKernelMap f G))
    (E : Sheaf (Opens.grothendieckTopology X) (Type u))
    (α' : E ⟶ (sheafForget (Opens.grothendieckTopology X)).obj (inverseImageX' sol))
    (α : E ⟶ FreeAlgebra.Presentation.generators (inverseImageStructureSheafUnder f))
    [Sheaf.IsLocallySurjective
      (FreeAlgebra.evaluation (inverseImageStructureSheafUnder f) E α).right]
    (hα : assignOf sol E α' = α),
      extClass sol E α' α hα = (extensionEquiv f G).symm (isoClassMk sol))

#check (AlgebraicGeometry.RingedSpace.Thickening.Solution.underlyingSets :
    (sol : Solution (𝟙 S) f G (zeroKernelMap f G)) →
      Sheaf (Opens.grothendieckTopology X) (Type u))

#check (AlgebraicGeometry.RingedSpace.Thickening.Solution.underlyingAssign' :
    (sol : Solution (𝟙 S) f G (zeroKernelMap f G)) →
      underlyingSets sol ⟶
        (sheafForget (Opens.grothendieckTopology X)).obj (inverseImageX' sol))

#check (AlgebraicGeometry.RingedSpace.Thickening.Solution.underlying_eval_isLocallySurjective :
    ∀ (sol : Solution (𝟙 S) f G (zeroKernelMap f G)),
      Sheaf.IsLocallySurjective
        (eval (underlyingSets sol)
          (assignOf sol (underlyingSets sol) (underlyingAssign' sol))))

#check (AlgebraicGeometry.RingedSpace.Thickening.Solution.eval_assignOf_isLocallySurjective :
    ∀ (sol : Solution (𝟙 S) f G (zeroKernelMap f G))
      (E : Sheaf (Opens.grothendieckTopology X) (Type u))
      (α' : E ⟶ (sheafForget (Opens.grothendieckTopology X)).obj (inverseImageX' sol))
      [Sheaf.IsLocallySurjective α'],
      Sheaf.IsLocallySurjective (eval E (assignOf sol E α')))

#check (SheafOfModules.RingedSite.NaiveCotangent.Presentation.derivedComparisonIso
    (B := inverseImageStructureSheafUnder f) :
    ∀ (E : Sheaf (Opens.grothendieckTopology X) (Type u))
      (α : E ⟶ FreeAlgebra.Presentation.generators (inverseImageStructureSheafUnder f))
      [Sheaf.IsLocallySurjective
        (FreeAlgebra.evaluation (inverseImageStructureSheafUnder f) E α).right],
      (DerivedCategory.Q (C := X.Modules)).obj (Presentation.ofGenerators (B := inverseImageStructureSheafUnder f) E α) ≅
        (DerivedCategory.Q (C := X.Modules)).obj NL[f])

#check (SheafOfModules.RingedSite.NaiveCotangent.Presentation.derivedComparisonIso_hom
    (B := inverseImageStructureSheafUnder f) :
    ∀ (E : Sheaf (Opens.grothendieckTopology X) (Type u))
      (α : E ⟶ FreeAlgebra.Presentation.generators (inverseImageStructureSheafUnder f))
      [Sheaf.IsLocallySurjective
        (FreeAlgebra.evaluation (inverseImageStructureSheafUnder f) E α).right],
      (Presentation.derivedComparisonIso (B := inverseImageStructureSheafUnder f) E α).hom =
        Presentation.derivedComparison (B := inverseImageStructureSheafUnder f) E α)

#check (AlgebraicGeometry.RingedSpace.Thickening.Solution.conormalHom :
    ∀ (sol : Solution (𝟙 S) f G (zeroKernelMap f G))
    (E : Sheaf (Opens.grothendieckTopology X) (Type u))
    (α' : E ⟶ (sheafForget (Opens.grothendieckTopology X)).obj (inverseImageX' sol))
    (α : E ⟶ FreeAlgebra.Presentation.generators (inverseImageStructureSheafUnder f))
    (hα : assignOf sol E α' = α),
      (Presentation.ofGenerators (B := inverseImageStructureSheafUnder f) E α).X (-1) ⟶ G)

end Solution
end AlgebraicGeometry.RingedSpace.Thickening
