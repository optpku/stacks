/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Remark_85_12_7_Warning_Abelian

/-!
# Remark 85.12.7 (Warning)

If only the two 1-cofaces `f_{δ 1}` and `f_{δ 0}` are flat, cartesian `O`-modules
form an abelian category by Lemma 85.12.5, but need not be a Serre subcategory of
`Mod(O)`: the inclusion need not be exact, unlike the all-coface case of Lemma 85.12.6.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open scoped Simplicial
open RingedSite
open CategoryTheory.SimplicialSites
open CategoryTheory.SimplicialSites.Module

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites.Module

section OfIsFlatDelta01

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [IsMorphismDiagram C J]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (ringedToposMap C J O φ).structureMap).IsRightAdjoint]
variable [∀ n, ToposHom.HasModulePullbackDerived (stageMorphism C J O n)]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (ringedToposMap C J O φ)]
variable [HasSheafify ((J ⦋0⦌).toGrothendieck) AddCommGrpCat.{w}]
variable [((J ⦋0⦌).toGrothendieck).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Remark 85.12.7 (Warning) (1)
In Situation 85.3.3, if only `f_{δ 1}` and `f_{δ 0}` are flat, then the category of
cartesian `O`-modules is abelian. This follows from Lemma 85.12.5: cartesian
`O`-modules are equivalent to face-descent pairs, whose kernels are `O_0`-module
kernels together with the kernel comparison of the two exact pullbacks. -/
@[stacks 0D7K]
instance instAbelian_of_isFlat_delta01
    [ToposHom.IsFlat (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2)))]
    [ToposHom.IsFlat (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2)))] :
    Abelian (Cartesian C J O) :=
  abelianOfEquivalence (cartesianEquivalence C J O).functor

end OfIsFlatDelta01

/-- Remark 85.12.7 (Warning) (2)
Lemma 85.12.6 notwithstanding, it can happen that the category of cartesian `O`-modules
is abelian without being a Serre subcategory of `Mod(O)`. Namely, in Situation 85.3.3,
if only `f_{δ 1}` and `f_{δ 0}` are flat, cartesian `O`-modules are abelian by
Lemma 85.12.5, but the inclusion into all `O`-modules need not be exact. This is
strictly weaker than the all-coface flatness used for a weak Serre class; non-flatness
of `ringedToposMap C J O (SimplexCategory.δ (0 : Fin 3))` is a typical obstruction,
not a hypothesis. -/
@[stacks 0D7K]
theorem not_forall_exactInclusion_of_isFlat_delta01 [UnivLE.{max u v, w}] :
    ¬ ∀ (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
      [IsMorphismDiagram C J]
      [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
      [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
        ((C.map φ).toFunctor).op.HasLeftKanExtension P]
      (O : Sheaf (topology C J) RingCat.{w})
      [(topology C J).HasSheafCompose (forget RingCat.{w})]
      [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
      [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
      [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
        (ofStage C n).op.HasPointwiseRightKanExtension P]
      [∀ n, (SheafOfModules.restrictScalars.{w}
        (stageMorphism C J O n).structureMap).IsRightAdjoint]
      [∀ {m n : SimplexCategory} (φ : m ⟶ n),
        (SheafOfModules.restrictScalars.{w}
          (ringedToposMap C J O φ).structureMap).IsRightAdjoint]
      [∀ n, ToposHom.HasModulePullbackDerived (stageMorphism C J O n)]
      [∀ {m n : SimplexCategory} (φ : m ⟶ n),
        ToposHom.HasModulePullbackDerived (ringedToposMap C J O φ)]
      [ToposHom.IsFlat (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2)))]
      [ToposHom.IsFlat (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2)))],
      exactFunctor (Cartesian C J O)
        (SheafOfModules.{w} (totalRingedSite C J O).structureSheaf)
        (cartesianProperty C J O).ι :=
  sorry

end CategoryTheory.SimplicialSites.Module
