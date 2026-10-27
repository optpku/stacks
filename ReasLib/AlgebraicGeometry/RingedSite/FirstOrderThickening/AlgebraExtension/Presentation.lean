/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.FirstOrderThickening.AlgebraExtension
public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent.Presentation.Ext
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Differentials.Conormal.SquareZero
public import ReasLib.CategoryTheory.Sites.AlgebraicSheaf.FreeAlgebra.Evaluation

/-!
# Polynomial presentations of square-zero algebra extensions on ringed sites

Lifted generators induce a polynomial-algebra map to the extension, a conormal map to its
identified kernel, and a derived extension class. The class agrees with the canonical
classification of the extension.
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

universe c v w u d

namespace SheafOfModules.RingedSite.FirstOrderThickening
namespace Solution

section Construction

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasWeakSheafify J CommRingCat.{w}]
variable [J.WEqualsLocallyBijective CommRingCat.{w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O_B O : Sheaf J CommRingCat.{w}}
variable {fSharp : O_B ⟶ O}
variable {G : SheafOfModules.{w} (ringSheaf J O)}

/-- Assignment of generators to `O` obtained by composing a lift `α' : E ⟶ O'` with the
underlying map of `S.proj`. -/
def assignOf
    (S : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G))
    (E : Sheaf J (Type w)) (α' : E ⟶ (sheafForget J).obj S.middle) :
    E ⟶ FreeAlgebra.Presentation.generators (Under.mk fSharp) :=
  α' ≫ (sheafForget J).map S.proj

/-- `assignOf` is postcomposition of the lift `α'` with the underlying map of `S.proj`. -/
theorem assignOf_eq
    (S : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G))
    (E : Sheaf J (Type w)) (α' : E ⟶ (sheafForget J).obj S.middle) :
    assignOf S E α' = α' ≫ (sheafForget J).map S.proj := rfl

/-- Evaluation `O_B[E] ⟶ O` determined by an assignment of generators to `O`. -/
abbrev eval (E : Sheaf J (Type w))
    (α : E ⟶ FreeAlgebra.Presentation.generators (Under.mk fSharp)) :
    FreeAlgebra.underlying O_B E ⟶ O :=
  (FreeAlgebra.evaluation (Under.mk fSharp) E α).right

/-- `eval` is the underlying ring map of free-algebra evaluation at `α`. -/
theorem eval_eq_evaluation (E : Sheaf J (Type w))
    (α : E ⟶ FreeAlgebra.Presentation.generators (Under.mk fSharp)) :
    eval E α = (FreeAlgebra.evaluation (Under.mk fSharp) E α).right := rfl

/-- Evaluation `O_B[E] ⟶ O'` determined by a lift of generators to the middle ring sheaf. -/
abbrev eval'
    (S : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G))
    (E : Sheaf J (Type w)) (α' : E ⟶ (sheafForget J).obj S.middle) :
    FreeAlgebra.underlying O_B E ⟶ S.middle :=
  (FreeAlgebra.evaluation (Under.mk S.structureMap) E α').right

/-- `eval'` is the underlying ring map of free-algebra evaluation at `α'`. -/
theorem eval'_eq_evaluation
    (S : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G))
    (E : Sheaf J (Type w)) (α' : E ⟶ (sheafForget J).obj S.middle) :
    eval' S E α' = (FreeAlgebra.evaluation (Under.mk S.structureMap) E α').right := rfl

/-- If the triangle `α' ≫ forget(S.proj) = α` commutes, then `eval' ≫ S.proj = eval`. -/
theorem eval'_comp_proj
    (S : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G))
    (E : Sheaf J (Type w)) (α' : E ⟶ (sheafForget J).obj S.middle)
    (α : E ⟶ FreeAlgebra.Presentation.generators (Under.mk fSharp))
    (hα : assignOf S E α' = α) :
    eval' S E α' ≫ S.proj = eval E α := by
  have hcomm : S.structureMap ≫ S.proj = fSharp :=
    S.commutes.trans (Category.id_comp fSharp)
  calc
    eval' S E α' ≫ S.proj = eval E (assignOf S E α') :=
      FreeAlgebra.evaluation_naturality (Under.mk S.structureMap) (Under.mk fSharp)
        (Under.homMk S.proj hcomm) E α'
    _ = eval E α := congrArg (eval E) hα

/-- A locally surjective lift of generators to a square-zero extension gives a locally
surjective evaluation onto the target ring sheaf. -/
theorem eval_assignOf_isLocallySurjective
    (S : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G))
    (E : Sheaf J (Type w)) (α' : E ⟶ (sheafForget J).obj S.middle)
    [Sheaf.IsLocallySurjective α'] :
    Sheaf.IsLocallySurjective (eval E (assignOf S E α')) := sorry

/-- Presentation morphism from the polynomial presentation of `fSharp` to the thickening
`S.proj`, determined by a triangle of generators. -/
def presentationHom
    (S : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G))
    (E : Sheaf J (Type w)) (α' : E ⟶ (sheafForget J).obj S.middle)
    (α : E ⟶ FreeAlgebra.Presentation.generators (Under.mk fSharp))
    (hα : assignOf S E α' = α) :
    Presentation.Hom (FreeAlgebra.base O_B E)
      (FreeAlgebra.evaluation (Under.mk fSharp) E α).right (𝟙 S.middle) S.proj where
  base := S.structureMap
  middle := eval' S E α'
  target := 𝟙 O
  baseSq := ⟨(Category.comp_id S.structureMap).trans
    (FreeAlgebra.evaluation_base (Under.mk S.structureMap) E α').symm⟩
  targetSq := ⟨(eval'_comp_proj S E α' α hα).trans (Category.comp_id (eval E α)).symm⟩

/-- The base map of `presentationHom` is the structure map of the solution. -/
theorem presentationHom_base
    (S : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G))
    (E : Sheaf J (Type w)) (α' : E ⟶ (sheafForget J).obj S.middle)
    (α : E ⟶ FreeAlgebra.Presentation.generators (Under.mk fSharp))
    (hα : assignOf S E α' = α) :
    (presentationHom S E α' α hα).base = S.structureMap := rfl

/-- The middle map of `presentationHom` is evaluation at the lift `α'`. -/
theorem presentationHom_middle
    (S : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G))
    (E : Sheaf J (Type w)) (α' : E ⟶ (sheafForget J).obj S.middle)
    (α : E ⟶ FreeAlgebra.Presentation.generators (Under.mk fSharp))
    (hα : assignOf S E α' = α) :
    (presentationHom S E α' α hα).middle = eval' S E α' := rfl

section Conormal

variable [HasSheafify J AddCommGrpCat.{w}]

/-- The map `J / J² ⟶ G` induced by the lift `α'` through the presentation morphism. -/
def conormalHom
    (S : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G))
    (E : Sheaf J (Type w)) (α' : E ⟶ (sheafForget J).obj S.middle)
    (α : E ⟶ FreeAlgebra.Presentation.generators (Under.mk fSharp))
    (hα : assignOf S E α' = α) :
    (Presentation.ofGenerators E α).X (-1) ⟶ G :=
  ((extendComplexIdIso O).inv.app (Presentation.ofGenerators E α) ≫
      Presentation.Hom.map (presentationHom S E α' α hα)).f (-1) ≫
    @SquareZeroExtension.conormalToTarget _ _ _ _ _ _ _ _ _ _ _ S.proj
      S.proj_locallySurjective S.proj_squareZero ≫ S.kernelIso.hom

/-- `conormalHom` is degree `-1` of the presentation map, followed by the square-zero
conormal identification with `G`. -/
theorem conormalHom_spec
    (S : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G))
    (E : Sheaf J (Type w)) (α' : E ⟶ (sheafForget J).obj S.middle)
    (α : E ⟶ FreeAlgebra.Presentation.generators (Under.mk fSharp))
    (hα : assignOf S E α' = α) :
    conormalHom S E α' α hα =
      ((extendComplexIdIso O).inv.app (Presentation.ofGenerators E α) ≫
          Presentation.Hom.map (presentationHom S E α' α hα)).f (-1) ≫
        @SquareZeroExtension.conormalToTarget _ _ _ _ _ _ _ _ _ _ _ S.proj
          S.proj_locallySurjective S.proj_squareZero ≫
          S.kernelIso.hom := rfl

section Derived

variable [HasDerivedCategory.{d} (SheafOfModules.{w} (ringSheaf J (Under.mk fSharp).right))]


/-- The `Ext¹` class of `conormalHom` on the presentation model `NL(α)`. -/
def presentationExtClass
    (S : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G))
    (E : Sheaf J (Type w)) (α' : E ⟶ (sheafForget J).obj S.middle)
    (α : E ⟶ FreeAlgebra.Presentation.generators (Under.mk fSharp))
    (hα : assignOf S E α' = α) :=
  conormalHomClass.{c, v, w, d} fSharp G E α (conormalHom S E α' α hα)

/-- `presentationExtClass` is `conormalHomClass` of `conormalHom`. -/
theorem presentationExtClass_def
    (S : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G))
    (E : Sheaf J (Type w)) (α' : E ⟶ (sheafForget J).obj S.middle)
    (α : E ⟶ FreeAlgebra.Presentation.generators (Under.mk fSharp))
    (hα : assignOf S E α' = α) :
    presentationExtClass S E α' α hα =
      conormalHomClass.{c, v, w, d} fSharp G E α (conormalHom S E α' α hα) := rfl

/-- The `Ext¹` class of the extension on `NL_{O / O_B}`, obtained by transporting
`presentationExtClass` along the derived presentation comparison. -/
def extClass
    (S : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G))
    (E : Sheaf J (Type w)) (α' : E ⟶ (sheafForget J).obj S.middle)
    (α : E ⟶ FreeAlgebra.Presentation.generators (Under.mk fSharp))
    [Sheaf.IsLocallySurjective (FreeAlgebra.evaluation (Under.mk fSharp) E α).right]
    (hα : assignOf S E α' = α) :
    Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.{d}.obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G)) :=
  (Presentation.derivedComparisonIso E α).inv ≫ presentationExtClass S E α' α hα

/-- Transporting `extClass` along the derived comparison recovers `presentationExtClass`. -/
theorem extClass_spec
    (S : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G))
    (E : Sheaf J (Type w)) (α' : E ⟶ (sheafForget J).obj S.middle)
    (α : E ⟶ FreeAlgebra.Presentation.generators (Under.mk fSharp))
    [Sheaf.IsLocallySurjective (FreeAlgebra.evaluation (Under.mk fSharp) E α).right]
    (hα : assignOf S E α' = α) :
    Presentation.derivedComparison E α ≫ extClass S E α' α hα =
      presentationExtClass S E α' α hα := by
  change Presentation.derivedComparison E α ≫
    (Presentation.derivedComparisonInv E α ≫ presentationExtClass S E α' α hα) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f ↦ f ≫ presentationExtClass S E α' α hα)
      (Presentation.derivedComparison_comp_derivedComparisonInv E α)).trans
        (Category.id_comp _))

end Derived

end Conormal

/-- Underlying sheaf of sets of the middle ring sheaf `O'` of a solution. -/
abbrev underlyingSets
    (S : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G)) :
    Sheaf J (Type w) :=
  (sheafForget J).obj S.middle

/-- The identity assignment of the underlying sheaf of sets of `O'`. -/
abbrev underlyingAssign'
    (S : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G)) :
    underlyingSets S ⟶ (sheafForget J).obj S.middle :=
  𝟙 _

/-- Using the underlying set sheaf of the middle ring sheaf with its identity lift gives a
locally surjective polynomial evaluation onto the target. -/
theorem underlying_eval_isLocallySurjective
    (S : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G)) :
    Sheaf.IsLocallySurjective
      (eval (underlyingSets S)
        (assignOf S (underlyingSets S) (underlyingAssign' S))) := by
  exact eval_assignOf_isLocallySurjective S (underlyingSets S) (underlyingAssign' S)

end Construction

section Classification

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

/-- The class induced by a lifted polynomial presentation of a square-zero algebra extension
is its class under the inverse of the canonical classification equivalence. -/
theorem extClass_eq_extensionEquiv_symm
    (S : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G))
    (E : Sheaf J (Type u)) (α' : E ⟶ (sheafForget J).obj S.middle)
    (α : E ⟶ FreeAlgebra.Presentation.generators (Under.mk fSharp))
    [Sheaf.IsLocallySurjective (FreeAlgebra.evaluation (Under.mk fSharp) E α).right]
    (hα : assignOf S E α' = α) :
    extClass S E α' α hα = (extensionEquiv fSharp G).symm (isoClassMk S) := sorry

end Classification

end Solution
end SheafOfModules.RingedSite.FirstOrderThickening
