/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_12_2_Cartesian
public import stacks_project.Chap85.Lemma_85_12_2_Comparison

/-!
# Lemma 85.12.2

In Situation 85.3.3, cartesianness of a sheaf of sets or abelian groups, an
object of `D(C_total)`, a sheaf of `O`-modules, or an object of `D(O)` is
equivalent to the comparison maps along coface operators `SimplexCategory.δ`
being isomorphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [IsMorphismDiagram C J]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (f : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map f).toFunctor).op.HasLeftKanExtension P]

/-- Lemma 85.12.2 (1)
In Situation 85.3.3, a sheaf `F` of sets on `C_total` is cartesian if and only if
`transition C J (SimplexCategory.δ j) F` is an isomorphism for every coface
`SimplexCategory.δ j`. -/
@[stacks 07TG]
theorem Sheaf.isCartesian_iff_delta (F : Sheaf (topology C J) (Type w)) :
    IsCartesian C J F ↔
      ∀ {n : ℕ} (j : Fin (n + 2)),
        IsIso (transition C J (SimplexCategory.δ j) F) :=
  sorry

/-- A sheaf of sets whose coface comparisons are isomorphisms is cartesian. -/
instance Sheaf.instIsCartesian_of_isIso_delta (F : Sheaf (topology C J) (Type w))
    [∀ (n : ℕ) (j : Fin (n + 2)),
      IsIso (transition C J (SimplexCategory.δ j) F)] :
    IsCartesian C J F :=
  sorry

section Abelian

variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (f : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map f).toFunctor).op.HasLeftKanExtension P]

/-- Lemma 85.12.2 (2)
In Situation 85.3.3, a sheaf `F` of abelian groups on `C_total` is cartesian if
and only if `abelianTransition C J (SimplexCategory.δ j) F` is an isomorphism
for every coface `SimplexCategory.δ j`. -/
@[stacks 07TG]
theorem abelian_isCartesian_iff_delta (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    Abelian.IsCartesian C J F ↔
      ∀ {n : ℕ} (j : Fin (n + 2)),
        IsIso (abelianTransition C J (SimplexCategory.δ j) F) :=
  sorry

/-- A sheaf of abelian groups whose coface comparisons are isomorphisms is cartesian. -/
instance instAbelianIsCartesian_of_isIso_delta
    (F : Sheaf (topology C J) AddCommGrpCat.{w})
    [∀ (n : ℕ) (j : Fin (n + 2)),
      IsIso (abelianTransition C J (SimplexCategory.δ j) F)] :
    Abelian.IsCartesian C J F :=
  sorry

section AbelianDerived

variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]

/-- Lemma 85.12.2 (3)
In Situation 85.3.3, an object `K` of `D(C_total)` is cartesian if and only if
`derivedTransition C J (SimplexCategory.δ j) K` is an isomorphism for every
coface `SimplexCategory.δ j`. -/
@[stacks 07TG]
theorem AbelianDerived.isCartesian_iff_delta
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})) :
    AbelianDerived.IsCartesian C J K ↔
      ∀ {n : ℕ} (j : Fin (n + 2)),
        IsIso (derivedTransition C J (SimplexCategory.δ j) K) :=
  sorry

/-- An object of `D(C_total)` whose coface comparisons are isomorphisms is cartesian. -/
instance AbelianDerived.instIsCartesian_of_isIso_delta
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
    [∀ (n : ℕ) (j : Fin (n + 2)),
      IsIso (derivedTransition C J (SimplexCategory.δ j) K)] :
    AbelianDerived.IsCartesian C J K :=
  sorry

end AbelianDerived

end Abelian

section Modules

variable [IsMorphismDiagram C J]
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (f : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (ringedToposMap C J O f).structureMap).IsRightAdjoint]
variable [∀ n, ToposHom.HasModulePullbackDerived (stageMorphism C J O n)]
variable [∀ {m n : SimplexCategory} (f : m ⟶ n),
    ToposHom.HasModulePullbackDerived (ringedToposMap C J O f)]

/-- Lemma 85.12.2 (4)
In Situation 85.3.3, if `O` is a sheaf of rings on `C_total`, a sheaf `F` of
`O`-modules is cartesian if and only if
`moduleTransition C J O (SimplexCategory.δ j) F` is an isomorphism for every
coface `SimplexCategory.δ j`. -/
@[stacks 07TG]
theorem Module.isCartesian_iff_delta
    (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf) :
    Module.IsCartesian C J O F ↔
      ∀ {n : ℕ} (j : Fin (n + 2)),
        IsIso (moduleTransition C J O (SimplexCategory.δ j) F) :=
  sorry

/-- An `O`-module whose coface comparisons are isomorphisms is cartesian. -/
instance Module.instIsCartesian_of_isIso_delta
    (F : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf)
    [∀ (n : ℕ) (j : Fin (n + 2)),
      IsIso (moduleTransition C J O (SimplexCategory.δ j) F)] :
    Module.IsCartesian C J O F :=
  sorry

/-- Lemma 85.12.2 (5)
In Situation 85.3.3, if `O` is a sheaf of rings on `C_total`, an object `K` of
`D(O)` is cartesian if and only if
`moduleDerivedTransition C J O (SimplexCategory.δ j) K` is an isomorphism for
every coface `SimplexCategory.δ j`. -/
@[stacks 07TG]
theorem ModuleDerived.isCartesian_iff_delta
    (K : Hom.ModuleDerived.{w} (totalRingedSite C J O)) :
    ModuleDerived.IsCartesian C J O K ↔
      ∀ {n : ℕ} (j : Fin (n + 2)),
        IsIso (moduleDerivedTransition C J O (SimplexCategory.δ j) K) :=
  sorry

/-- An object of `D(O)` whose coface comparisons are isomorphisms is cartesian. -/
instance ModuleDerived.instIsCartesian_of_isIso_delta
    (K : Hom.ModuleDerived.{w} (totalRingedSite C J O))
    [∀ (n : ℕ) (j : Fin (n + 2)),
      IsIso (moduleDerivedTransition C J O (SimplexCategory.δ j) K)] :
    ModuleDerived.IsCartesian C J O K :=
  sorry

end Modules

end CategoryTheory.SimplicialSites
