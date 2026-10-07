module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
public import stacks_project.Chap85.Lemma_85_11_1_Flat
public import stacks_project.Chap85.Lemma_85_12_4_Equivalence
public import stacks_project.Chap85.Lemma_85_12_5_Equivalence

/-!
# Lemma 85.12.6

In Situation 85.3.3, cartesian abelian sheaves on `C_total` form a weak Serre
subcategory of `Ab(C_total)` and are closed under colimits. If the coface
morphisms of ringed topoi are flat, the same holds for cartesian `O`-modules in
`Mod(O)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open RingedSite

noncomputable section

universe u v w u' v'

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [IsMorphismDiagram C J]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]

namespace Sheaf

variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]

/-- Lemma 85.12.6 (1)
In Situation 85.3.3, the full subcategory of cartesian abelian sheaves forms a
weak Serre subcategory of `Ab(C_total) := Sheaf (topology C J) AddCommGrpCat.{w}`. -/
@[stacks 0D7J]
instance cartesianProperty_isWeakSerreClass :
    IsWeakSerreClass (cartesianProperty C J AddCommGrpCat.{w}) :=
  sorry

/-- Lemma 85.12.6 (2)
In Situation 85.3.3, colimits of systems of cartesian abelian sheaves on `C_total`
are cartesian. -/
@[stacks 0D7J]
instance cartesianProperty_isClosedUnderColimitsOfShape
    (ι : Type u') [Category.{v'} ι] :
    (cartesianProperty C J AddCommGrpCat.{w}).IsClosedUnderColimitsOfShape ι :=
  sorry

/-- The inclusion of cartesian abelian sheaves into `Ab(C_total)` is exact. -/
theorem cartesianProperty_inclusion_exact :
    exactFunctor (cartesianProperty C J AddCommGrpCat.{w}).FullSubcategory
      (Sheaf (topology C J) AddCommGrpCat.{w})
      (cartesianProperty C J AddCommGrpCat.{w}).ι :=
  sorry

/-- The kernel of a morphism of cartesian abelian sheaves is cartesian. -/
instance isCartesian_kernel {F G : Sheaf (topology C J) AddCommGrpCat.{w}}
    (f : F ⟶ G) [IsCartesian C J F] [IsCartesian C J G] :
    IsCartesian C J (kernel f) :=
  sorry

/-- The cokernel of a morphism of cartesian abelian sheaves is cartesian. -/
instance isCartesian_cokernel {F G : Sheaf (topology C J) AddCommGrpCat.{w}}
    (f : F ⟶ G) [IsCartesian C J F] [IsCartesian C J G] :
    IsCartesian C J (cokernel f) :=
  sorry

/-- In a short exact sequence of abelian sheaves on `C_total`, if the outer terms
are cartesian then so is the middle. -/
theorem isCartesian_of_shortExact
    {S : ShortComplex (Sheaf (topology C J) AddCommGrpCat.{w})} (hS : S.ShortExact)
    (h₁ : IsCartesian C J S.X₁) (h₃ : IsCartesian C J S.X₃) :
    IsCartesian C J S.X₂ :=
  sorry

end Sheaf

namespace Module

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

section WeakSerre

variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [(topology C J).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ {n : ℕ} (j : Fin (n + 2)),
    ToposHom.IsFlat (ringedToposMap C J O (SimplexCategory.δ j))]

/-- Lemma 85.12.6 (3)
In Situation 85.3.3, let `O` be a sheaf of rings on `C_total` such that the coface
morphisms `f_δ^n_j := ringedToposMap C J O (SimplexCategory.δ j)` of ringed topoi
are flat. Then the full subcategory of cartesian `O`-modules forms a weak Serre
subcategory of
`Mod(O) := SheafOfModules.{w} (totalRingedSite C J O).structureSheaf`. -/
@[stacks 0D7J]
instance cartesianProperty_isWeakSerreClass :
    IsWeakSerreClass (cartesianProperty C J O) :=
  sorry

/-- The inclusion of cartesian `O`-modules into `Mod(O)` is exact. -/
theorem cartesianProperty_inclusion_exact :
    exactFunctor (cartesianProperty C J O).FullSubcategory
      (SheafOfModules.{w} (totalRingedSite C J O).structureSheaf)
      (cartesianProperty C J O).ι :=
  sorry

/-- The kernel of a morphism of cartesian `O`-modules is cartesian. -/
instance isCartesian_kernel
    {F G : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf}
    (f : F ⟶ G) [IsCartesian C J O F] [IsCartesian C J O G] :
    IsCartesian C J O (kernel f) :=
  sorry

/-- The cokernel of a morphism of cartesian `O`-modules is cartesian. -/
instance isCartesian_cokernel
    {F G : SheafOfModules.{w} (totalRingedSite C J O).structureSheaf}
    (f : F ⟶ G) [IsCartesian C J O F] [IsCartesian C J O G] :
    IsCartesian C J O (cokernel f) :=
  sorry

/-- In a short exact sequence of `O`-modules, if the outer terms are cartesian then
so is the middle. -/
theorem isCartesian_of_shortExact
    {S : ShortComplex (SheafOfModules.{w} (totalRingedSite C J O).structureSheaf)}
    (hS : S.ShortExact) (h₁ : IsCartesian C J O S.X₁) (h₃ : IsCartesian C J O S.X₃) :
    IsCartesian C J O S.X₂ :=
  sorry

end WeakSerre

/-- Lemma 85.12.6 (4)
In Situation 85.3.3, let `O` be a sheaf of rings on `C_total`. Colimits of
systems of cartesian `O`-modules are cartesian. -/
@[stacks 0D7J]
instance cartesianProperty_isClosedUnderColimitsOfShape
    (ι : Type u') [Category.{v'} ι] :
    (cartesianProperty C J O).IsClosedUnderColimitsOfShape ι :=
  sorry

end Module

end CategoryTheory.SimplicialSites
