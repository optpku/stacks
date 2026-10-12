/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Definition_85_12_1_Cartesian
public import stacks_project.Chap85.Lemma_85_11_1_Flat

/-!
# Lemma 85.14.5

In Situation 85.3.3, a map of objects of `D(O)` out of a cartesian object
is zero once it vanishes in degree `0` and the indicated stage Hom-groups vanish,
provided every simplex-operator structure map `f_φ⁻¹ O_n ⟶ O_m` is flat.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial
open RingedSite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [instMorphismDiagram : IsMorphismDiagram C J]
variable [instWeakSheafify : ∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [instLeftKan : ∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
include instMorphismDiagram instWeakSheafify instLeftKan
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

/-- Lemma 85.14.5
In Situation 85.3.3, let `O` be a sheaf of rings on `C_total` and let
`K, K'` be objects of `D(O)` with `K` cartesian. If `f_φ⁻¹ O_n ⟶ O_m` is
flat for every simplex operator `φ`, `Hom(K_i⟦i⟧, K'_i) = 0` for `i > 0`
and `Hom(K_i⟦i + 1⟧, K'_i) = 0` for `i ≥ 0`, then any map `K ⟶ K'`
inducing the zero map `K_0 ⟶ K'_0` is zero. -/
@[stacks 0D9R]
theorem cartesianModuleDerived_hom_eq_zero
    (K K' : Hom.ModuleDerived.{w} (totalRingedSite C J O))
    [ModuleDerived.IsCartesian C J O K]
    (h_flat : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      ToposHom.IsFlat (ringedToposMap C J O φ))
    (h_hom : ∀ n : SimplexCategory, 0 < n.len →
      Subsingleton (((moduleDerivedComponent C J O n).obj K)⟦(n.len : ℤ)⟧ ⟶
        (moduleDerivedComponent C J O n).obj K'))
    (h_hom_succ : ∀ n : SimplexCategory,
      Subsingleton (((moduleDerivedComponent C J O n).obj K)⟦(n.len + 1 : ℤ)⟧ ⟶
        (moduleDerivedComponent C J O n).obj K'))
    (f : K ⟶ K') (hf0 : (moduleDerivedComponent C J O ⦋0⦌).map f = 0) :
    f = 0 :=
  sorry

/-- Maps `K ⟶ K'` out of a cartesian object of `D(O)` that agree on the
degree-`0` component are equal, under the flatness and stage Hom-vanishing
hypotheses of `cartesianModuleDerived_hom_eq_zero`. -/
theorem cartesianModuleDerived_hom_eq_of_eq_component
    (K K' : Hom.ModuleDerived.{w} (totalRingedSite C J O))
    [ModuleDerived.IsCartesian C J O K]
    (h_flat : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      ToposHom.IsFlat (ringedToposMap C J O φ))
    (h_hom : ∀ n : SimplexCategory, 0 < n.len →
      Subsingleton (((moduleDerivedComponent C J O n).obj K)⟦(n.len : ℤ)⟧ ⟶
        (moduleDerivedComponent C J O n).obj K'))
    (h_hom_succ : ∀ n : SimplexCategory,
      Subsingleton (((moduleDerivedComponent C J O n).obj K)⟦(n.len + 1 : ℤ)⟧ ⟶
        (moduleDerivedComponent C J O n).obj K'))
    (f g : K ⟶ K')
    (hfg : (moduleDerivedComponent C J O ⦋0⦌).map f =
      (moduleDerivedComponent C J O ⦋0⦌).map g) :
    f = g :=
  sorry

end CategoryTheory.SimplicialSites
