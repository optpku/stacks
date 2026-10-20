/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Differentials.Conormal.SquareZero
public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent.Presentation.Derived
public import stacks_project.Chap91.Lemma_91_13_2_ConormalClass
public import stacks_project.Chap91.Lemma_91_13_4

/-!
# Presentation chart of a square-zero identity-diagram extension

A commutative triangle of sheaves of sets `E ⟶ O' ⟶ O` presents the naive cotangent
complex of `fSharp` by the two-term complex of the polynomial algebra `O_B[E]`. The lift
to `O'` induces the conormal map `J / J² ⟶ G` whose `Ext¹` class is the class of the
extension.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.FirstOrderThickening
open SheafOfModules.RingedSite.FirstOrderThickening.Solution
open SheafOfModules.RingedSite.NaiveCotangent
open scoped DerivedExt SheafOfModules.RingedSite
open scoped CategoryTheory.Sheaf.FreeAlgebra

noncomputable section

universe u

namespace SheafOfModules.RingedSite.FirstOrderThickening
namespace Solution

-- Local instance justification (defeq pin): `moduleCat_hasDerivedCategory` is reducible to `HasDerivedCategory.standard` and is not global; `ModuleDerived`, `singleFunctor`, and Ext must share that same derived-category instance.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
-- Local instance justification (defeq pin): the commutative-sheaf presentation uses the same standard derived-category owner, exposed through the site-level spelling.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O_B O : Sheaf J CommRingCat.{u}}
variable {fSharp : O_B ⟶ O}
variable {G : SheafOfModules (ringSheaf J O)}

/-- Assignment of generators to `O` obtained by composing a lift `α' : E ⟶ O'` with the
underlying map of `S.proj`. -/
def assignOf
    (S : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G))
    (E : Sheaf J (Type u)) (α' : E ⟶ (sheafForget J).obj S.middle) :
    E ⟶ FreeAlgebra.Presentation.generators (Under.mk fSharp) :=
  α' ≫ (sheafForget J).map S.proj

/-- `assignOf` is postcomposition of the lift `α'` with the underlying map of `S.proj`. -/
theorem assignOf_eq
    (S : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G))
    (E : Sheaf J (Type u)) (α' : E ⟶ (sheafForget J).obj S.middle) :
    assignOf S E α' = α' ≫ (sheafForget J).map S.proj := sorry

/-- Evaluation `O_B[E] ⟶ O` determined by an assignment of generators to `O`. -/
abbrev eval (E : Sheaf J (Type u))
    (α : E ⟶ FreeAlgebra.Presentation.generators (Under.mk fSharp)) :
    FreeAlgebra.underlying O_B E ⟶ O :=
  (FreeAlgebra.evaluation (Under.mk fSharp) E α).right

/-- `eval` is the underlying ring map of free-algebra evaluation at `α`. -/
theorem eval_eq_evaluation (E : Sheaf J (Type u))
    (α : E ⟶ FreeAlgebra.Presentation.generators (Under.mk fSharp)) :
    eval E α = (FreeAlgebra.evaluation (Under.mk fSharp) E α).right := sorry

/-- Evaluation `O_B[E] ⟶ O'` determined by a lift of generators to the middle ring sheaf. -/
abbrev eval'
    (S : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G))
    (E : Sheaf J (Type u)) (α' : E ⟶ (sheafForget J).obj S.middle) :
    FreeAlgebra.underlying O_B E ⟶ S.middle :=
  (FreeAlgebra.evaluation (Under.mk S.structureMap) E α').right

/-- `eval'` is the underlying ring map of free-algebra evaluation at `α'`. -/
theorem eval'_eq_evaluation
    (S : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G))
    (E : Sheaf J (Type u)) (α' : E ⟶ (sheafForget J).obj S.middle) :
    eval' S E α' = (FreeAlgebra.evaluation (Under.mk S.structureMap) E α').right := sorry

/-- If the triangle `α' ≫ forget(S.proj) = α` commutes, then `eval' ≫ S.proj = eval`. -/
theorem eval'_comp_proj
    (S : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G))
    (E : Sheaf J (Type u)) (α' : E ⟶ (sheafForget J).obj S.middle)
    (α : E ⟶ FreeAlgebra.Presentation.generators (Under.mk fSharp))
    (hα : assignOf S E α' = α) :
    eval' S E α' ≫ S.proj = eval E α := sorry

/-- Presentation morphism from the polynomial presentation of `fSharp` to the thickening
`S.proj`, determined by a triangle of generators. -/
def presentationHom
    (S : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G))
    (E : Sheaf J (Type u)) (α' : E ⟶ (sheafForget J).obj S.middle)
    (α : E ⟶ FreeAlgebra.Presentation.generators (Under.mk fSharp))
    (hα : assignOf S E α' = α) :
    Presentation.Hom (FreeAlgebra.base O_B E)
      (FreeAlgebra.evaluation (Under.mk fSharp) E α).right (𝟙 S.middle) S.proj where
  base := S.structureMap
  middle := eval' S E α'
  target := 𝟙 O
  baseSq := ⟨sorry⟩
  targetSq := ⟨sorry⟩

/-- The base map of `presentationHom` is the structure map of the solution. -/
theorem presentationHom_base
    (S : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G))
    (E : Sheaf J (Type u)) (α' : E ⟶ (sheafForget J).obj S.middle)
    (α : E ⟶ FreeAlgebra.Presentation.generators (Under.mk fSharp))
    (hα : assignOf S E α' = α) :
    (presentationHom S E α' α hα).base = S.structureMap := sorry

/-- The middle map of `presentationHom` is evaluation at the lift `α'`. -/
theorem presentationHom_middle
    (S : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G))
    (E : Sheaf J (Type u)) (α' : E ⟶ (sheafForget J).obj S.middle)
    (α : E ⟶ FreeAlgebra.Presentation.generators (Under.mk fSharp))
    (hα : assignOf S E α' = α) :
    (presentationHom S E α' α hα).middle = eval' S E α' := sorry

/-- The map `J / J² ⟶ G` induced by the lift `α'` through the presentation morphism. -/
def conormalHom
    (S : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G))
    (E : Sheaf J (Type u)) (α' : E ⟶ (sheafForget J).obj S.middle)
    (α : E ⟶ FreeAlgebra.Presentation.generators (Under.mk fSharp))
    (hα : assignOf S E α' = α) :
    (Presentation.ofGenerators E α).X (-1) ⟶ G :=
  ((extendComplexIdIso O).inv.app (Presentation.ofGenerators E α) ≫
      Presentation.Hom.map (presentationHom S E α' α hα)).f (-1) ≫
    SquareZeroExtension.conormalToTarget S.proj S.proj_squareZero ≫ S.kernelIso.hom

/-- `conormalHom` is degree `-1` of the presentation map, followed by the square-zero
conormal identification with `G`. -/
theorem conormalHom_spec
    (S : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G))
    (E : Sheaf J (Type u)) (α' : E ⟶ (sheafForget J).obj S.middle)
    (α : E ⟶ FreeAlgebra.Presentation.generators (Under.mk fSharp))
    (hα : assignOf S E α' = α) :
    conormalHom S E α' α hα =
      ((extendComplexIdIso O).inv.app (Presentation.ofGenerators E α) ≫
          Presentation.Hom.map (presentationHom S E α' α hα)).f (-1) ≫
        SquareZeroExtension.conormalToTarget S.proj S.proj_squareZero ≫
          S.kernelIso.hom := sorry

/-- The `Ext¹` class of `conormalHom` on the presentation model `NL(α)`. -/
def presentationExtClass
    (S : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G))
    (E : Sheaf J (Type u)) (α' : E ⟶ (sheafForget J).obj S.middle)
    (α : E ⟶ FreeAlgebra.Presentation.generators (Under.mk fSharp))
    (hα : assignOf S E α' = α) :=
  conormalHomClass fSharp G E α (conormalHom S E α' α hα)

/-- `presentationExtClass` is `conormalHomClass` of `conormalHom`. -/
theorem presentationExtClass_def
    (S : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G))
    (E : Sheaf J (Type u)) (α' : E ⟶ (sheafForget J).obj S.middle)
    (α : E ⟶ FreeAlgebra.Presentation.generators (Under.mk fSharp))
    (hα : assignOf S E α' = α) :
    presentationExtClass S E α' α hα =
      conormalHomClass fSharp G E α (conormalHom S E α' α hα) := sorry

/-- The `Ext¹` class of the extension on `NL_{O / O_B}`, obtained by transporting
`presentationExtClass` along the derived presentation comparison. -/
def extClass
    (S : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G))
    (E : Sheaf J (Type u)) (α' : E ⟶ (sheafForget J).obj S.middle)
    (α : E ⟶ FreeAlgebra.Presentation.generators (Under.mk fSharp))
    [Sheaf.IsLocallySurjective (FreeAlgebra.evaluation (Under.mk fSharp) E α).right]
    (hα : assignOf S E α' = α) :
    Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G)) :=
  (Presentation.derivedComparisonIso E α).inv ≫ presentationExtClass S E α' α hα

/-- Transporting `extClass` along the derived comparison recovers `presentationExtClass`. -/
theorem extClass_spec
    (S : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G))
    (E : Sheaf J (Type u)) (α' : E ⟶ (sheafForget J).obj S.middle)
    (α : E ⟶ FreeAlgebra.Presentation.generators (Under.mk fSharp))
    [Sheaf.IsLocallySurjective (FreeAlgebra.evaluation (Under.mk fSharp) E α).right]
    (hα : assignOf S E α' = α) :
    Presentation.derivedComparison E α ≫ extClass S E α' α hα =
      presentationExtClass S E α' α hα := sorry

/-- Underlying sheaf of sets of the middle ring sheaf `O'` of a solution. -/
abbrev underlyingSets
    (S : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G)) :
    Sheaf J (Type u) :=
  (sheafForget J).obj S.middle

/-- The identity assignment of the underlying sheaf of sets of `O'`. -/
abbrev underlyingAssign'
    (S : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G)) :
    underlyingSets S ⟶ (sheafForget J).obj S.middle :=
  𝟙 _

/-- The source example `E = forget(O')`, `α' = 𝟙` makes `O_B[E] ⟶ O` locally surjective. -/
instance underlying_eval_isLocallySurjective
    (S : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G)) :
    Sheaf.IsLocallySurjective
      (eval (underlyingSets S)
        (assignOf S (underlyingSets S) (underlyingAssign' S))) := sorry

end Solution
end SheafOfModules.RingedSite.FirstOrderThickening
