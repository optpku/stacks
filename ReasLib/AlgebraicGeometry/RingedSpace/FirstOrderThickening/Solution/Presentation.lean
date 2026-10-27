/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Solution.AlgebraExtension
public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent.Presentation.Ext

/-!
# Presentation chart of a square-zero identity-diagram ringed-space extension

A locally surjective polynomial evaluation arising from a commutative triangle
`E ⟶ i⁻¹𝒪_{X'} ⟶ 𝒪_X` presents `NL[f]` by the two-term complex of
`f⁻¹𝒪_S[E]`. The lift to `i⁻¹𝒪_{X'}` induces the conormal map `J / J² ⟶ 𝒢`
whose `Ext¹` class is the class of the extension.
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

/-- Assignment of generators to `𝒪_X` obtained by composing a lift
`α' : E ⟶ i⁻¹𝒪_{X'}` with the underlying map of `sol.i^♯`. -/
def assignOf (sol : Solution (𝟙 S) f G (zeroKernelMap f G))
    (E : Sheaf (Opens.grothendieckTopology X) (Type u))
    (α' : E ⟶ (sheafForget (Opens.grothendieckTopology X)).obj (inverseImageX' sol)) :
    E ⟶ FreeAlgebra.Presentation.generators (inverseImageStructureSheafUnder f) :=
  α' ≫ (sheafForget (Opens.grothendieckTopology X)).map
    (inverseImageStructureSheafHomComm sol.i)

/-- `assignOf` is postcomposition of the lift `α'` with the underlying map of `sol.i^♯`. -/
theorem assignOf_eq (sol : Solution (𝟙 S) f G (zeroKernelMap f G))
    (E : Sheaf (Opens.grothendieckTopology X) (Type u))
    (α' : E ⟶ (sheafForget (Opens.grothendieckTopology X)).obj (inverseImageX' sol)) :
    assignOf sol E α' =
      α' ≫ (sheafForget (Opens.grothendieckTopology X)).map
        (inverseImageStructureSheafHomComm sol.i) := rfl

/-- Evaluation `f⁻¹𝒪_S[E] ⟶ 𝒪_X` determined by an assignment of generators to `𝒪_X`. -/
abbrev eval (E : Sheaf (Opens.grothendieckTopology X) (Type u))
    (α : E ⟶ FreeAlgebra.Presentation.generators (inverseImageStructureSheafUnder f)) :
    FreeAlgebra.underlying
      ((TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj S.sheaf) E ⟶ X.sheaf :=
  (FreeAlgebra.evaluation (inverseImageStructureSheafUnder f) E α).right

/-- `eval` is the underlying ring map of free-algebra evaluation at `α`. -/
theorem eval_eq_evaluation (E : Sheaf (Opens.grothendieckTopology X) (Type u))
    (α : E ⟶ FreeAlgebra.Presentation.generators (inverseImageStructureSheafUnder f)) :
    eval E α = (FreeAlgebra.evaluation (inverseImageStructureSheafUnder f) E α).right := rfl

/-- Coefficient map `f⁻¹𝒪_S ⟶ i⁻¹𝒪_{X'}` of the identity-diagram extension. -/
def structureMap (sol : Solution (𝟙 S) f G (zeroKernelMap f G)) :
    (TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj S.sheaf ⟶ inverseImageX' sol :=
  (TopCat.Sheaf.pullbackCongr (A := CommRingCat.{u})
      (congrArg (fun k : X ⟶ S ↦ k.hom.base)
        (Category.comp_id f).symm)).hom.app S.sheaf ≫
    (inverseImageS'IsoComposite sol).inv ≫ inverseImageS'ToX' sol

/-- `structureMap` identifies `f⁻¹𝒪_S` with `(f ≫ 𝟙 S)⁻¹𝒪_S` and then uses
`inverseImageS'ToX'`. -/
theorem structureMap_spec (sol : Solution (𝟙 S) f G (zeroKernelMap f G)) :
    structureMap sol =
      (TopCat.Sheaf.pullbackCongr (A := CommRingCat.{u})
          (congrArg (fun k : X ⟶ S ↦ k.hom.base)
            (Category.comp_id f).symm)).hom.app S.sheaf ≫
        (inverseImageS'IsoComposite sol).inv ≫ inverseImageS'ToX' sol := rfl

/-- Evaluation `f⁻¹𝒪_S[E] ⟶ i⁻¹𝒪_{X'}` determined by a lift of generators. -/
abbrev eval' (sol : Solution (𝟙 S) f G (zeroKernelMap f G))
    (E : Sheaf (Opens.grothendieckTopology X) (Type u))
    (α' : E ⟶ (sheafForget (Opens.grothendieckTopology X)).obj (inverseImageX' sol)) :
    FreeAlgebra.underlying
      ((TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj S.sheaf) E ⟶
      inverseImageX' sol :=
  (FreeAlgebra.evaluation (Under.mk (structureMap sol)) E α').right

/-- `eval'` is the underlying ring map of free-algebra evaluation at `α'`. -/
theorem eval'_eq_evaluation (sol : Solution (𝟙 S) f G (zeroKernelMap f G))
    (E : Sheaf (Opens.grothendieckTopology X) (Type u))
    (α' : E ⟶ (sheafForget (Opens.grothendieckTopology X)).obj (inverseImageX' sol)) :
    eval' sol E α' = (FreeAlgebra.evaluation (Under.mk (structureMap sol)) E α').right := rfl

/-- If the triangle `α' ≫ forget(sol.i^♯) = α` commutes, then `eval' ≫ sol.i^♯ = eval`. -/
theorem eval'_comp_proj (sol : Solution (𝟙 S) f G (zeroKernelMap f G))
    (E : Sheaf (Opens.grothendieckTopology X) (Type u))
    (α' : E ⟶ (sheafForget (Opens.grothendieckTopology X)).obj (inverseImageX' sol))
    (α : E ⟶ FreeAlgebra.Presentation.generators (inverseImageStructureSheafUnder f))
    (hα : assignOf sol E α' = α) :
    eval' sol E α' ≫ inverseImageStructureSheafHomComm sol.i = eval E α := sorry

/-- The coefficient map and polynomial evaluation commute. -/
theorem presentationHom_baseSq (sol : Solution (𝟙 S) f G (zeroKernelMap f G))
    (E : Sheaf (Opens.grothendieckTopology X) (Type u))
    (α' : E ⟶ (sheafForget (Opens.grothendieckTopology X)).obj (inverseImageX' sol))
    (α : E ⟶ FreeAlgebra.Presentation.generators (inverseImageStructureSheafUnder f))
    (hα : assignOf sol E α' = α) :
    FreeAlgebra.base ((TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj S.sheaf) E ≫
      eval' sol E α' = structureMap sol ≫ 𝟙 (inverseImageX' sol) := sorry

/-- Polynomial evaluation commutes with reduction to the given assignment. -/
theorem presentationHom_targetSq (sol : Solution (𝟙 S) f G (zeroKernelMap f G))
    (E : Sheaf (Opens.grothendieckTopology X) (Type u))
    (α' : E ⟶ (sheafForget (Opens.grothendieckTopology X)).obj (inverseImageX' sol))
    (α : E ⟶ FreeAlgebra.Presentation.generators (inverseImageStructureSheafUnder f))
    (hα : assignOf sol E α' = α) :
    (FreeAlgebra.evaluation (inverseImageStructureSheafUnder f) E α).right ≫ 𝟙 X.sheaf =
      eval' sol E α' ≫ inverseImageStructureSheafHomComm sol.i := sorry

/-- Presentation morphism from the polynomial presentation of `f` to the thickening
`sol.i`, determined by a triangle of generators. -/
def presentationHom (sol : Solution (𝟙 S) f G (zeroKernelMap f G))
    (E : Sheaf (Opens.grothendieckTopology X) (Type u))
    (α' : E ⟶ (sheafForget (Opens.grothendieckTopology X)).obj (inverseImageX' sol))
    (α : E ⟶ FreeAlgebra.Presentation.generators (inverseImageStructureSheafUnder f))
    (hα : assignOf sol E α' = α) :
    Presentation.Hom
      (FreeAlgebra.base ((TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj S.sheaf) E)
      (FreeAlgebra.evaluation (inverseImageStructureSheafUnder f) E α).right
      (𝟙 (inverseImageX' sol)) (inverseImageStructureSheafHomComm sol.i) where
  base := structureMap sol
  middle := eval' sol E α'
  target := 𝟙 X.sheaf
  baseSq := ⟨(presentationHom_baseSq sol E α' α hα).symm⟩
  targetSq := ⟨(presentationHom_targetSq sol E α' α hα).symm⟩

/-- The base map of `presentationHom` is the coefficient map of the solution. -/
theorem presentationHom_base (sol : Solution (𝟙 S) f G (zeroKernelMap f G))
    (E : Sheaf (Opens.grothendieckTopology X) (Type u))
    (α' : E ⟶ (sheafForget (Opens.grothendieckTopology X)).obj (inverseImageX' sol))
    (α : E ⟶ FreeAlgebra.Presentation.generators (inverseImageStructureSheafUnder f))
    (hα : assignOf sol E α' = α) :
    (presentationHom sol E α' α hα).base = structureMap sol := rfl

/-- The middle map of `presentationHom` is evaluation at the lift `α'`. -/
theorem presentationHom_middle (sol : Solution (𝟙 S) f G (zeroKernelMap f G))
    (E : Sheaf (Opens.grothendieckTopology X) (Type u))
    (α' : E ⟶ (sheafForget (Opens.grothendieckTopology X)).obj (inverseImageX' sol))
    (α : E ⟶ FreeAlgebra.Presentation.generators (inverseImageStructureSheafUnder f))
    (hα : assignOf sol E α' = α) :
    (presentationHom sol E α' α hα).middle = eval' sol E α' := rfl

/-- Degree `-1` of the presentation map, as a map into the conormal sheaf of `sol.i`. -/
def presentationConormal (sol : Solution (𝟙 S) f G (zeroKernelMap f G))
    (E : Sheaf (Opens.grothendieckTopology X) (Type u))
    (α' : E ⟶ (sheafForget (Opens.grothendieckTopology X)).obj (inverseImageX' sol))
    (α : E ⟶ FreeAlgebra.Presentation.generators (inverseImageStructureSheafUnder f))
    (hα : assignOf sol E α' = α) :
    (Presentation.ofGenerators (B := inverseImageStructureSheafUnder f) E α).X (-1) ⟶ Hom.conormalSheaf sol.i :=
  ((extendComplexIdIso X.sheaf).inv.app (Presentation.ofGenerators (B := inverseImageStructureSheafUnder f) E α) ≫
    Presentation.Hom.map (presentationHom sol E α' α hα)).f (-1)

/-- `presentationConormal` is degree `-1` of the presentation map. -/
theorem presentationConormal_spec (sol : Solution (𝟙 S) f G (zeroKernelMap f G))
    (E : Sheaf (Opens.grothendieckTopology X) (Type u))
    (α' : E ⟶ (sheafForget (Opens.grothendieckTopology X)).obj (inverseImageX' sol))
    (α : E ⟶ FreeAlgebra.Presentation.generators (inverseImageStructureSheafUnder f))
    (hα : assignOf sol E α' = α) :
    presentationConormal sol E α' α hα =
      ((extendComplexIdIso X.sheaf).inv.app (Presentation.ofGenerators (B := inverseImageStructureSheafUnder f) E α) ≫
        Presentation.Hom.map (presentationHom sol E α' α hα)).f (-1) := rfl

/-- The map `J / J² ⟶ 𝒢` induced by the lift `α'` through the presentation morphism. -/
def conormalHom (sol : Solution (𝟙 S) f G (zeroKernelMap f G))
    (E : Sheaf (Opens.grothendieckTopology X) (Type u))
    (α' : E ⟶ (sheafForget (Opens.grothendieckTopology X)).obj (inverseImageX' sol))
    (α : E ⟶ FreeAlgebra.Presentation.generators (inverseImageStructureSheafUnder f))
    (hα : assignOf sol E α' = α) :
    (Presentation.ofGenerators (B := inverseImageStructureSheafUnder f) E α).X (-1) ⟶ G :=
  presentationConormal sol E α' α hα ≫
    conormalToIdeal sol ≫ sol.kernelIso.hom

/-- `conormalHom` is degree `-1` of the presentation map, followed by the square-zero
conormal identification with `𝒢`. -/
theorem conormalHom_spec (sol : Solution (𝟙 S) f G (zeroKernelMap f G))
    (E : Sheaf (Opens.grothendieckTopology X) (Type u))
    (α' : E ⟶ (sheafForget (Opens.grothendieckTopology X)).obj (inverseImageX' sol))
    (α : E ⟶ FreeAlgebra.Presentation.generators (inverseImageStructureSheafUnder f))
    (hα : assignOf sol E α' = α) :
    conormalHom sol E α' α hα =
      presentationConormal sol E α' α hα ≫
        conormalToIdeal sol ≫ sol.kernelIso.hom := rfl

/-- The `Ext¹` class of `conormalHom` on the presentation model `NL(α)`. -/
def presentationExtClass (sol : Solution (𝟙 S) f G (zeroKernelMap f G))
    (E : Sheaf (Opens.grothendieckTopology X) (Type u))
    (α' : E ⟶ (sheafForget (Opens.grothendieckTopology X)).obj (inverseImageX' sol))
    (α : E ⟶ FreeAlgebra.Presentation.generators (inverseImageStructureSheafUnder f))
    (hα : assignOf sol E α' = α) :=
  SheafOfModules.RingedSite.NaiveCotangent.conormalHomClass
    (inverseImageStructureSheafUnder f).hom G E α (conormalHom sol E α' α hα)

/-- `presentationExtClass` is `conormalHomClass` of `conormalHom`. -/
theorem presentationExtClass_def (sol : Solution (𝟙 S) f G (zeroKernelMap f G))
    (E : Sheaf (Opens.grothendieckTopology X) (Type u))
    (α' : E ⟶ (sheafForget (Opens.grothendieckTopology X)).obj (inverseImageX' sol))
    (α : E ⟶ FreeAlgebra.Presentation.generators (inverseImageStructureSheafUnder f))
    (hα : assignOf sol E α' = α) :
    presentationExtClass sol E α' α hα =
      SheafOfModules.RingedSite.NaiveCotangent.conormalHomClass
        (inverseImageStructureSheafUnder f).hom G E α
        (conormalHom sol E α' α hα) := rfl

/-- The `Ext¹` class of the extension on `NL[f]`, obtained by transporting
`presentationExtClass` along the derived presentation comparison. -/
def extClass (sol : Solution (𝟙 S) f G (zeroKernelMap f G))
    (E : Sheaf (Opens.grothendieckTopology X) (Type u))
    (α' : E ⟶ (sheafForget (Opens.grothendieckTopology X)).obj (inverseImageX' sol))
    (α : E ⟶ FreeAlgebra.Presentation.generators (inverseImageStructureSheafUnder f))
    [Sheaf.IsLocallySurjective
      (FreeAlgebra.evaluation (inverseImageStructureSheafUnder f) E α).right]
    (hα : assignOf sol E α' = α) :
    Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := X.Modules)).obj NL[f],
      (DerivedCategory.Q (C := X.Modules)).obj ((CochainComplex.singleFunctor X.Modules 0).obj G)) :=
  (Presentation.derivedComparisonIso E α).inv ≫ presentationExtClass sol E α' α hα

/-- Transporting `extClass` along the derived comparison recovers `presentationExtClass`. -/
theorem extClass_spec (sol : Solution (𝟙 S) f G (zeroKernelMap f G))
    (E : Sheaf (Opens.grothendieckTopology X) (Type u))
    (α' : E ⟶ (sheafForget (Opens.grothendieckTopology X)).obj (inverseImageX' sol))
    (α : E ⟶ FreeAlgebra.Presentation.generators (inverseImageStructureSheafUnder f))
    [Sheaf.IsLocallySurjective
      (FreeAlgebra.evaluation (inverseImageStructureSheafUnder f) E α).right]
    (hα : assignOf sol E α' = α) :
    Presentation.derivedComparison E α ≫ extClass sol E α' α hα =
      presentationExtClass sol E α' α hα := sorry

/-- A locally surjective lift of generators to a square-zero extension induces a locally
surjective polynomial evaluation on the quotient. -/
theorem eval_assignOf_isLocallySurjective
    (sol : Solution (𝟙 S) f G (zeroKernelMap f G))
    (E : Sheaf (Opens.grothendieckTopology X) (Type u))
    (α' : E ⟶ (sheafForget (Opens.grothendieckTopology X)).obj (inverseImageX' sol))
    [Sheaf.IsLocallySurjective α'] :
    Sheaf.IsLocallySurjective (eval E (assignOf sol E α')) := sorry

/-- Underlying sheaf of sets of the inverse image `i⁻¹𝒪_{X'}`. -/
abbrev underlyingSets (sol : Solution (𝟙 S) f G (zeroKernelMap f G)) :
    Sheaf (Opens.grothendieckTopology X) (Type u) :=
  (sheafForget (Opens.grothendieckTopology X)).obj (inverseImageX' sol)

/-- The identity assignment of the underlying sheaf of sets of `i⁻¹𝒪_{X'}`. -/
abbrev underlyingAssign' (sol : Solution (𝟙 S) f G (zeroKernelMap f G)) :
    underlyingSets sol ⟶
      (sheafForget (Opens.grothendieckTopology X)).obj (inverseImageX' sol) :=
  𝟙 _

/-- Evaluation on the underlying sheaf of sets of the extension, reduced along its
projection, is locally surjective. -/
theorem underlying_eval_isLocallySurjective
    (sol : Solution (𝟙 S) f G (zeroKernelMap f G)) :
    Sheaf.IsLocallySurjective
      (eval (underlyingSets sol)
        (assignOf sol (underlyingSets sol) (underlyingAssign' sol))) := sorry

/-- The class determined by a lifted polynomial presentation is the class of the
square-zero extension under the canonical Ext¹ classification. -/
theorem extClass_eq_extensionEquiv_symm
    (sol : Solution (𝟙 S) f G (zeroKernelMap f G))
    (E : Sheaf (Opens.grothendieckTopology X) (Type u))
    (α' : E ⟶ (sheafForget (Opens.grothendieckTopology X)).obj (inverseImageX' sol))
    (α : E ⟶ FreeAlgebra.Presentation.generators (inverseImageStructureSheafUnder f))
    [Sheaf.IsLocallySurjective
      (FreeAlgebra.evaluation (inverseImageStructureSheafUnder f) E α).right]
    (hα : assignOf sol E α' = α) :
    extClass sol E α' α hα = (extensionEquiv f G).symm (isoClassMk sol) := sorry

end Solution
end AlgebraicGeometry.RingedSpace.Thickening
