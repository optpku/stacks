/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_14_2_System
public import stacks_project.Chap85.Lemma_85_11_1_Flat

/-!
# Lemma 85.14.7

In Situation 85.3.3, a cartesian simplicial system of the derived category of
modules with flat structure maps `f_φ⁻¹ O_m ⟶ O_n` for every `φ : m ⟶ n`
(equivalently `f_φ⁻¹ O_n ⟶ O_m` for `φ : n ⟶ m`, as in Lemma 85.6.3) and
vanishing `Hom(K_i⟦t⟧, K_i)` for `t > 0` comes from a cartesian object of `D(O)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.SimplicialSites
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

/-- Lemma 85.14.7
In Situation 85.3.3, let `O` be a sheaf of rings on `C_total`. Let `(K_n, K_φ)`
be a cartesian simplicial system of the derived category of modules such that
for every `φ : m ⟶ n` the structure map of `ringedToposMap C J O φ`, namely
`f_φ⁻¹ O_m ⟶ O_n`, is flat (the same family as `f_φ⁻¹ O_n ⟶ O_m` for
`φ : n ⟶ m`, as in Lemma 85.6.3) and `Hom(K_i⟦t⟧, K_i) = 0` for every stage
`i` and every `t > 0`. Then there exists a cartesian object `K` of `D(O)` whose
associated simplicial system is isomorphic to `(K_n, K_φ)`. -/
@[stacks 0D9T]
theorem exists_isCartesian_of_derivedModuleSystem
    (Ksys : DerivedModuleSystemOnComponents C J O)
    [DerivedModuleSystem.IsCartesian Ksys]
    (h_flat : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      ToposHom.IsFlat (ringedToposMap C J O φ))
    (h_hom : ∀ (n : SimplexCategory) (t : ℤ), 0 < t →
      Subsingleton ((Ksys.obj n)⟦t⟧ ⟶ Ksys.obj n)) :
    ∃ (K : Hom.ModuleDerived.{w} (totalRingedSite C J O))
      (α : DerivedModuleSystem.Hom (toDerivedModuleSystem C J O K) Ksys),
      ModuleDerived.IsCartesian C J O K ∧ ∀ n, IsIso (α.app n) :=
  sorry

end CategoryTheory.SimplicialSites
