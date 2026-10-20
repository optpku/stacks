module

public import ReasLib.Algebra.Category.ModuleCat.CellReplacement
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Cochain
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-!
# Unbounded left-derived functors on module categories from the displayed cell model

@stack 064M
@stack 05S9

Let `F : ModuleCat R ⥤ D` be an additive functor. The input complex is replaced by the actual
cell replacement `ModuleCat.CellReplacement.replacement`, `F` is applied degreewise and the result
is localized; native localization descends this to `D(R) ⥤ D(D)`. At every object of the
homotopy category, the pointwise left-derived limit is the displayed cone of this functor, and its
lift map is evaluation at the specified cell augmentation. Hence the existence certificates
`HasPointwiseLeftDerivedFunctor` and `HasLeftDerivedFunctor` store actual limit cones and lift
maps rather than admitted existence.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v uR uD vD wD

namespace CategoryTheory.Functor.ModuleCatCellModel

variable {R : Type uR} [Ring R] [Small.{v} R]
variable {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
variable (F : ModuleCat.{v} R ⥤ D) [F.Additive]

/-- The given functor applied degreewise, before replacing the input. -/
def ordinaryCochain : CochainComplex (ModuleCat.{v} R) ℤ ⥤ DerivedCategory D :=
  F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q

/-- The displayed cell replacement, degreewise functor, and actual localization. -/
def cochain : CochainComplex (ModuleCat.{v} R) ℤ ⥤ DerivedCategory D :=
  ModuleCat.CellReplacement.functor R ⋙ ordinaryCochain F

/-- Applying an additive functor to the cell-replacement map of a quasi-isomorphism gives a
quasi-isomorphism: the replacement map is a homotopy equivalence between K-projective complexes,
and additive functors preserve that homotopy equivalence. -/
theorem map_replacementMap_quasiIso
    {K L : CochainComplex (ModuleCat.{v} R) ℤ} (f : K ⟶ L) (hf : QuasiIso f) :
    QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (ModuleCat.CellReplacement.replacementMap f)) := sorry

/-- The image of a quasi-isomorphism is inverted by the formal localization of its specified
cell-replacement map. -/
theorem cochain_inverts :
    (HomologicalComplex.quasiIso (ModuleCat.{v} R) (ComplexShape.up ℤ)).IsInvertedBy
      (cochain F) := by
  intro K L f hf
  exact (Localization.isoOfHom
    (DerivedCategory.Q (C := D))
    (HomologicalComplex.quasiIso D (ComplexShape.up ℤ))
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (ModuleCat.CellReplacement.replacementMap f))
    (map_replacementMap_quasiIso F f hf)).isIso_hom

/-- The actual localization of the displayed model functor. -/
def derived : DerivedCategory (ModuleCat.{v} R) ⥤ DerivedCategory D :=
  Localization.lift (cochain F) (cochain_inverts F) (DerivedCategory.Q (C := ModuleCat.{v} R))

/-- The native localization comparison keeps all specified cell-model maps. -/
def fac : DerivedCategory.Q ⋙ derived F ≅ cochain F :=
  Localization.fac (cochain F) (cochain_inverts F) (DerivedCategory.Q (C := ModuleCat.{v} R))

/-- The cochain counit is degreewise application to the specified augmentation. -/
def counit : DerivedCategory.Q ⋙ derived F ⟶ ordinaryCochain F :=
  (fac F).hom ≫
    Functor.whiskerRight (ModuleCat.CellReplacement.augmentationNatTrans R) (ordinaryCochain F) ≫
      (Functor.leftUnitor (ordinaryCochain F)).hom

/-- The homotopy counit component uses the same cell augmentation and native quotient map. -/
def homotopyCounitComponent (K : HomotopyCategory (ModuleCat.{v} R) (ComplexShape.up ℤ)) :
    (derived F).obj (DerivedCategory.Qh.obj K) ⟶ (Functor.Homotopy.toDerived F).obj K :=
  (derived F).map ((DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)).hom.app K.as) ≫
    (counit F).app K.as ≫ (Functor.Homotopy.cochainIso F).inv.app K.as

/-- The component formula respects chain homotopy. -/
theorem homotopyCounitComponent_naturality
    {K L : HomotopyCategory (ModuleCat.{v} R) (ComplexShape.up ℤ)} (a : K ⟶ L) :
    (DerivedCategory.Qh ⋙ derived F).map a ≫ homotopyCounitComponent F L =
      homotopyCounitComponent F K ≫ (Functor.Homotopy.toDerived F).map a := sorry

/-- The homotopy counit retains the actual cochain augmentation maps. -/
def homotopyCounit : DerivedCategory.Qh ⋙ derived F ⟶ Functor.Homotopy.toDerived F where
  app K := homotopyCounitComponent F K
  naturality := fun _ _ a ↦ homotopyCounitComponent_naturality F a

/-- The displayed right extension of the homotopy-to-derived functor. -/
def rightExtension :
    Functor.RightExtension (DerivedCategory.Qh (C := ModuleCat.{v} R))
      (Functor.Homotopy.toDerived F) :=
  Functor.RightExtension.mk (derived F) (homotopyCounit F)

/-- Formal inversion of the actual cell augmentation of `X` in the derived category. -/
def inputAugmentationIso (X : HomotopyCategory (ModuleCat.{v} R) (ComplexShape.up ℤ)) :
    DerivedCategory.Qh.obj ((HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)).obj
        (ModuleCat.CellReplacement.replacement X.as)) ≅ DerivedCategory.Qh.obj X :=
  Localization.isoOfHom DerivedCategory.Qh
    (HomotopyCategory.quasiIso (ModuleCat.{v} R) (ComplexShape.up ℤ))
    ((HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)).map
      (ModuleCat.CellReplacement.augmentation X.as))
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr
      (ModuleCat.CellReplacement.augmentation_quasiIso X.as))

/-- The structured arrow at `X` given by the inverse of the specified cell augmentation. -/
def modelArrow (X : HomotopyCategory (ModuleCat.{v} R) (ComplexShape.up ℤ)) :
    StructuredArrow (DerivedCategory.Qh.obj X) (DerivedCategory.Qh (C := ModuleCat.{v} R)) :=
  StructuredArrow.mk (inputAugmentationIso X).inv

/-- Evaluation of `F` on the cell replacement of `X` is the derived value at `X`: the native
cochain comparison, then the localization comparison, then the native quotient comparison. -/
def modelValue (X : HomotopyCategory (ModuleCat.{v} R) (ComplexShape.up ℤ)) :
    (Functor.Homotopy.toDerived F).obj (modelArrow X).right ⟶
      (derived F).obj (DerivedCategory.Qh.obj X) :=
  (Functor.Homotopy.cochainIso F).hom.app (ModuleCat.CellReplacement.replacement X.as) ≫
    ((fac F).app X.as).inv ≫
      (derived F).map ((DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)).inv.app X.as)

/-- The displayed cone of the derived functor at `X`. -/
def cone (X : HomotopyCategory (ModuleCat.{v} R) (ComplexShape.up ℤ)) :
    Cone (StructuredArrow.proj (DerivedCategory.Qh.obj X) DerivedCategory.Qh ⋙
      Functor.Homotopy.toDerived F) :=
  (rightExtension F).coneAt (DerivedCategory.Qh.obj X)

/-- The lift into the displayed cone evaluates the given cone at the inverse cell augmentation. -/
def coneLift (X : HomotopyCategory (ModuleCat.{v} R) (ComplexShape.up ℤ))
    (s : Cone (StructuredArrow.proj (DerivedCategory.Qh.obj X) DerivedCategory.Qh ⋙
      Functor.Homotopy.toDerived F)) :
    s.pt ⟶ (cone F X).pt :=
  s.π.app (modelArrow X) ≫ modelValue F X

/-- The specified lift factors every cone leg. -/
theorem coneLift_fac (X : HomotopyCategory (ModuleCat.{v} R) (ComplexShape.up ℤ))
    (s : Cone (StructuredArrow.proj (DerivedCategory.Qh.obj X) DerivedCategory.Qh ⋙
      Functor.Homotopy.toDerived F))
    (g : StructuredArrow (DerivedCategory.Qh.obj X) DerivedCategory.Qh) :
    coneLift F X s ≫ (cone F X).π.app g = s.π.app g := sorry

/-- The specified lift is the unique factorization. -/
theorem coneLift_uniq (X : HomotopyCategory (ModuleCat.{v} R) (ComplexShape.up ℤ))
    (s : Cone (StructuredArrow.proj (DerivedCategory.Qh.obj X) DerivedCategory.Qh ⋙
      Functor.Homotopy.toDerived F))
    (m : s.pt ⟶ (cone F X).pt) (hm : ∀ g, m ≫ (cone F X).π.app g = s.π.app g) :
    m = coneLift F X s := sorry

/-- The displayed cone is a limit, with the specified lift. -/
def coneIsLimit (X : HomotopyCategory (ModuleCat.{v} R) (ComplexShape.up ℤ)) :
    IsLimit (cone F X) where
  lift s := coneLift F X s
  fac s g := coneLift_fac F X s g
  uniq s m hm := coneLift_uniq F X s m hm

/-- The pointwise left-derived certificate stores the displayed limit cone. -/
@[stacks 05S9 "pointwise derived functor from the displayed cell model"]
instance hasPointwiseLeftDerivedFunctorAt
    (X : HomotopyCategory (ModuleCat.{v} R) (ComplexShape.up ℤ)) :
    (Functor.Homotopy.toDerived F).HasPointwiseLeftDerivedFunctorAt
      (HomotopyCategory.quasiIso (ModuleCat.{v} R) (ComplexShape.up ℤ)) X :=
  ((Functor.Homotopy.toDerived F).hasPointwiseLeftDerivedFunctorAt_iff DerivedCategory.Qh
    (HomotopyCategory.quasiIso (ModuleCat.{v} R) (ComplexShape.up ℤ)) X).mpr
      (HasLimit.mk ⟨cone F X, coneIsLimit F X⟩)

/-- The everywhere-pointwise left-derived certificate. -/
@[stacks 05S9 "everywhere pointwise derived functor from the displayed cell model"]
theorem hasPointwiseLeftDerivedFunctor :
    (Functor.Homotopy.toDerived F).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso (ModuleCat.{v} R) (ComplexShape.up ℤ)) :=
  fun X ↦ hasPointwiseLeftDerivedFunctorAt F X

/-- The total left-derived certificate obtained from the displayed pointwise limit cones. -/
@[stacks 05S9 "total derived functor from the displayed cell model"]
theorem hasLeftDerivedFunctor :
    (Functor.Homotopy.toDerived F).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (ModuleCat.{v} R) (ComplexShape.up ℤ)) :=
  letI := hasPointwiseLeftDerivedFunctor F
  Functor.hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor _ _

end CategoryTheory.Functor.ModuleCatCellModel
