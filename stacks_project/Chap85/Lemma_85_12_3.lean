/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Arbitrary
public import stacks_project.Chap85.Definition_85_12_1_Cartesian
public import stacks_project.Chap85.Lemma_85_4_2_MorphismDiagram
public import stacks_project.Chap85.Lemma_85_11_1_Component
public import stacks_project.Chap85.Lemma_85_12_3_Pullback

/-!
# Lemma 85.12.3

In Situation 85.3.3, with an augmentation towards a site `D` as in Remark 85.4.1,
pullbacks of sheaves of sets or abelian groups, objects of `D(D)`, `O_D`-modules,
and objects of `D(O_D)` along the total augmentation morphism are cartesian.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [IsMorphismDiagram.{u, v, max u v} C J]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type (max u v))]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type (max u v)),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]

section InverseImage

variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable (u0 : D ⥤ C.obj ⦋0⦌)
variable [HasWeakSheafify K.toGrothendieck (Type (max u v))]
variable [HasWeakSheafify (topology C J) (Type (max u v))]
variable [∀ P : Dᵒᵖ ⥤ Type (max u v), u0.op.HasLeftKanExtension P]
variable [∀ (n : SimplexCategory) (P : Dᵒᵖ ⥤ Type (max u v)),
    (IsAugmentation.stageFunctor C u0 n).op.HasLeftKanExtension P]
variable [HasEqualizers (Sheaf K.toGrothendieck (Type (max u v)))]
variable [IsAugmentation.{u, v, max u v} C J K u0]

/-- Lemma 85.12.3 (1)
In Situation 85.3.3, with an augmentation `a0` towards a site `D` as in
Remark 85.4.1, the pullback `a⁻¹ G` of a sheaf of sets on `D` is cartesian. -/
@[stacks 0D7H]
instance inverseImage_isCartesian (G : Sheaf K.toGrothendieck (Type (max u v))) :
    IsCartesian C J ((IsAugmentation.inverseImage.{u, v, max u v} C J K u0).obj G) :=
  sorry

section Abelian

variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{max u v}]
variable [∀ (n : SimplexCategory) (P : Dᵒᵖ ⥤ AddCommGrpCat.{max u v}),
    (IsAugmentation.stageFunctor C u0 n).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{max u v}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [HasSheafify K.toGrothendieck AddCommGrpCat.{max u v}]
variable [HasSheafify (topology C J) AddCommGrpCat.{max u v}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{max u v}]

/-- Lemma 85.12.3 (2)
In Situation 85.3.3, with an augmentation `a0` towards a site `D` as in
Remark 85.4.1, the pullback `a⁻¹ G` of a sheaf of abelian groups on `D` is
cartesian. -/
@[stacks 0D7H]
instance abelianInverseImage_isCartesian
    (G : Sheaf K.toGrothendieck AddCommGrpCat.{max u v}) :
    Abelian.IsCartesian C J
      ((IsAugmentation.abelianInverseImage.{u, v, max u v} C J K u0).obj G) :=
  sorry

/-- Lemma 85.12.3 (3)
In Situation 85.3.3, with an augmentation `a0` towards a site `D` as in
Remark 85.4.1, the pullback `a⁻¹ dK` of an object of `D(D)` is cartesian. -/
@[stacks 0D7H]
instance derivedInverseImage_isCartesian
    (dK : DerivedCategory (Sheaf K.toGrothendieck AddCommGrpCat.{max u v})) :
    Derived.IsCartesian C J
      ((IsAugmentation.derivedInverseImage.{u, v, max u v} C J K u0).obj dK) :=
  sorry

end Abelian

section Modules

variable (O : Sheaf (topology C J) RingCat.{max u v})
variable (O_D : Sheaf K.toGrothendieck RingCat.{max u v})
variable [(topology C J).HasSheafCompose (forget RingCat.{max u v})]
variable [K.toGrothendieck.HasSheafCompose (forget RingCat.{max u v})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{max u v})]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type (max u v))]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type (max u v),
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{max u v}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{max u v}
      (ringedToposMap C J O φ).structureMap).IsRightAdjoint]
variable [∀ n, ToposHom.HasModulePullbackDerived (stageMorphism C J O n)]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (ringedToposMap C J O φ)]
variable (a : ToposHom (totalRingedSite C J O) (ofRingSheaf K.toGrothendieck O_D))
variable [(SheafOfModules.restrictScalars.{max u v} a.structureMap).IsRightAdjoint]
variable [ToposHom.HasModulePullbackDerived a]

/-- Lemma 85.12.3 (4)
In Situation 85.3.3, with an augmentation `a0` towards a site `D` as in
Remark 85.4.1, if `O` is a sheaf of rings on `C_total`, `O_D` is a sheaf of rings
on `D`, and `a^♯` is the Section 85.11 morphism `O_D ⟶ a_* O`, the pullback
`a^* F` of a sheaf of `O_D`-modules is cartesian. -/
@[stacks 0D7H]
theorem modulePullback_isCartesian
    (h_inverseImage :
      a.toTopos.inverseImage ≅ IsAugmentation.inverseImage.{u, v, max u v} C J K u0)
    (h_stageComp : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      ToposHom.TwoIso
        ((ringedToposMap C J O φ).comp (augmentationComponent C J O a m))
        (augmentationComponent C J O a n))
    (F : SheafOfModules.{max u v} O_D) :
    Module.IsCartesian C J O (a.modulePullback.obj F) :=
  sorry

/-- Lemma 85.12.3 (5)
In Situation 85.3.3, with an augmentation `a0` towards a site `D` as in
Remark 85.4.1, if `O` is a sheaf of rings on `C_total`, `O_D` is a sheaf of rings
on `D`, and `a^♯` is the Section 85.11 morphism `O_D ⟶ a_* O`, the derived
pullback `La^* dK` of an object of `D(O_D)` is cartesian. -/
@[stacks 0D7H]
theorem modulePullbackDerived_isCartesian
    (h_inverseImage :
      a.toTopos.inverseImage ≅ IsAugmentation.inverseImage.{u, v, max u v} C J K u0)
    (h_stageComp : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      ToposHom.TwoIso
        ((ringedToposMap C J O φ).comp (augmentationComponent C J O a m))
        (augmentationComponent C J O a n))
    (dK : Hom.ModuleDerived.{max u v} (ofRingSheaf K.toGrothendieck O_D)) :
    ModuleDerived.IsCartesian C J O (a.modulePullbackDerived.obj dK) :=
  sorry

end Modules

end InverseImage

end CategoryTheory.SimplicialSites
