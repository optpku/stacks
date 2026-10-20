module

public import ReasLib.RingTheory.CotangentComplex.Atiyah.PrincipalParts
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Derived
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CellReplacement.Functorial
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Cochain
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import ReasLib.CategoryTheory.Functor.Derived.Total.Triangulated

/-!
# Derived scalar extension along a simplicial polynomial augmentation

The displayed cell replacement and its augmentation specify the functor, counit,
pointwise cones and cone lifts for derived degreewise scalar extension.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace Algebra.CotangentComplex.Atiyah

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- Degreewise scalar extension along the polynomial augmentation is additive. -/
instance extensionDegreewise_additive : (extensionDegreewise A B).Additive := sorry

namespace DerivedExtensionModel

/-- The given functor applied degreewise, before replacing the input. -/
private def ordinary : CochainComplex (PresheafOfModules.{u} (standardSimplicialRing A B)) ℤ ⥤ DerivedCategory (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) :=
  (extensionDegreewise A B).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q

/-- The displayed cell replacement, degreewise functor, and actual localization. -/
private def cochain : CochainComplex (PresheafOfModules.{u} (standardSimplicialRing A B)) ℤ ⥤ DerivedCategory (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) :=
  PresheafOfModules.CellReplacement.functor (R := standardSimplicialRing A B) ⋙ ordinary A B

/-- Applying degreewise scalar extension to the cell-replacement map of a quasi-isomorphism gives a
quasi-isomorphism: the displayed cell tower is objectwise a free cell resolution, and scalar extension
preserves homotopy equivalences of these objectwise cell resolutions. -/
private theorem map_replacementMap_quasiIso
    {K L : CochainComplex (PresheafOfModules.{u} (standardSimplicialRing A B)) ℤ} (f : K ⟶ L) (hf : QuasiIso f) :
    QuasiIso (((extensionDegreewise A B).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (PresheafOfModules.CellReplacement.replacementMap f)) := sorry

/-- The image of a quasi-isomorphism is inverted by the formal localization of its specified
cell-replacement map. -/
private theorem inverts :
    (HomologicalComplex.quasiIso (PresheafOfModules.{u} (standardSimplicialRing A B)) (ComplexShape.up ℤ)).IsInvertedBy
      (cochain A B) := by
  intro K L f hf
  exact (Localization.isoOfHom
    (DerivedCategory.Q (C := SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B))
    (HomologicalComplex.quasiIso (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) (ComplexShape.up ℤ))
    (((extensionDegreewise A B).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (PresheafOfModules.CellReplacement.replacementMap f))
    (map_replacementMap_quasiIso A B f hf)).isIso_hom

/-- The actual localization of the displayed model functor. -/
private def functor : DerivedCategory (PresheafOfModules.{u} (standardSimplicialRing A B)) ⥤ DerivedCategory (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) :=
  Localization.lift (cochain A B) (inverts A B) (DerivedCategory.Q (C := PresheafOfModules.{u} (standardSimplicialRing A B)))

/-- The native localization comparison keeps all specified cell-model maps. -/
private def fac : DerivedCategory.Q ⋙ functor A B ≅ cochain A B :=
  Localization.fac (cochain A B) (inverts A B) (DerivedCategory.Q (C := PresheafOfModules.{u} (standardSimplicialRing A B)))

/-- The cochain counit is degreewise application to the specified augmentation. -/
private def counit : DerivedCategory.Q ⋙ functor A B ⟶ ordinary A B :=
  (fac A B).hom ≫
    Functor.whiskerRight (PresheafOfModules.CellReplacement.augmentationNatTrans (R := standardSimplicialRing A B)) (ordinary A B) ≫
      (Functor.leftUnitor (ordinary A B)).hom

/-- The homotopy counit component uses the same cell augmentation and native quotient map. -/
private def homotopyCounitComponent (K : HomotopyCategory (PresheafOfModules.{u} (standardSimplicialRing A B)) (ComplexShape.up ℤ)) :
    (functor A B).obj (DerivedCategory.Qh.obj K) ⟶ (Functor.Homotopy.toDerived (extensionDegreewise A B)).obj K :=
  (functor A B).map ((DerivedCategory.quotientCompQhIso (PresheafOfModules.{u} (standardSimplicialRing A B))).hom.app K.as) ≫
    (counit A B).app K.as ≫ (Functor.Homotopy.cochainIso (extensionDegreewise A B)).inv.app K.as

/-- The component formula respects chain homotopy. -/
private theorem homotopyCounitComponent_naturality
    {K L : HomotopyCategory (PresheafOfModules.{u} (standardSimplicialRing A B)) (ComplexShape.up ℤ)} (a : K ⟶ L) :
    (DerivedCategory.Qh ⋙ functor A B).map a ≫ homotopyCounitComponent A B L =
      homotopyCounitComponent A B K ≫ (Functor.Homotopy.toDerived (extensionDegreewise A B)).map a := sorry

/-- The homotopy counit retains the actual cochain augmentation maps. -/
private def homotopyCounit : DerivedCategory.Qh ⋙ functor A B ⟶ Functor.Homotopy.toDerived (extensionDegreewise A B) where
  app K := homotopyCounitComponent A B K
  naturality := fun _ _ a ↦ homotopyCounitComponent_naturality A B a

/-- The displayed right extension of the homotopy-to-derived functor. -/
private def rightExtension :
    Functor.RightExtension (DerivedCategory.Qh (C := PresheafOfModules.{u} (standardSimplicialRing A B)))
      (Functor.Homotopy.toDerived (extensionDegreewise A B)) :=
  Functor.RightExtension.mk (functor A B) (homotopyCounit A B)

/-- Formal inversion of the actual cell augmentation of `X` in the derived category. -/
private def inputAugmentationIso (X : HomotopyCategory (PresheafOfModules.{u} (standardSimplicialRing A B)) (ComplexShape.up ℤ)) :
    DerivedCategory.Qh.obj ((HomotopyCategory.quotient (PresheafOfModules.{u} (standardSimplicialRing A B)) (ComplexShape.up ℤ)).obj
        (PresheafOfModules.CellReplacement.replacement X.as)) ≅ DerivedCategory.Qh.obj X :=
  Localization.isoOfHom DerivedCategory.Qh
    (HomotopyCategory.quasiIso (PresheafOfModules.{u} (standardSimplicialRing A B)) (ComplexShape.up ℤ))
    ((HomotopyCategory.quotient (PresheafOfModules.{u} (standardSimplicialRing A B)) (ComplexShape.up ℤ)).map
      (PresheafOfModules.CellReplacement.augmentation X.as))
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr
      (PresheafOfModules.CellReplacement.augmentation_quasiIso X.as))

/-- The structured arrow at `X` given by the inverse of the specified cell augmentation. -/
private def arrow (X : HomotopyCategory (PresheafOfModules.{u} (standardSimplicialRing A B)) (ComplexShape.up ℤ)) :
    StructuredArrow (DerivedCategory.Qh.obj X) (DerivedCategory.Qh (C := PresheafOfModules.{u} (standardSimplicialRing A B))) :=
  StructuredArrow.mk (inputAugmentationIso A B X).inv

/-- Evaluation of scalar extension on the cell replacement of `X` is the derived value at `X`: the native
cochain comparison, then the localization comparison, then the native quotient comparison. -/
private def value (X : HomotopyCategory (PresheafOfModules.{u} (standardSimplicialRing A B)) (ComplexShape.up ℤ)) :
    (Functor.Homotopy.toDerived (extensionDegreewise A B)).obj (arrow A B X).right ⟶
      (functor A B).obj (DerivedCategory.Qh.obj X) :=
  (Functor.Homotopy.cochainIso (extensionDegreewise A B)).hom.app (PresheafOfModules.CellReplacement.replacement X.as) ≫
    ((fac A B).app X.as).inv ≫
      (functor A B).map ((DerivedCategory.quotientCompQhIso (PresheafOfModules.{u} (standardSimplicialRing A B))).inv.app X.as)

/-- The displayed cone of the derived functor at `X`. -/
private def cone (X : HomotopyCategory (PresheafOfModules.{u} (standardSimplicialRing A B)) (ComplexShape.up ℤ)) :
    Cone (StructuredArrow.proj (DerivedCategory.Qh.obj X) DerivedCategory.Qh ⋙
      Functor.Homotopy.toDerived (extensionDegreewise A B)) :=
  (rightExtension A B).coneAt (DerivedCategory.Qh.obj X)

/-- The lift into the displayed cone evaluates the given cone at the inverse cell augmentation. -/
private def lift (X : HomotopyCategory (PresheafOfModules.{u} (standardSimplicialRing A B)) (ComplexShape.up ℤ))
    (s : Cone (StructuredArrow.proj (DerivedCategory.Qh.obj X) DerivedCategory.Qh ⋙
      Functor.Homotopy.toDerived (extensionDegreewise A B))) :
    s.pt ⟶ (cone A B X).pt :=
  s.π.app (arrow A B X) ≫ value A B X

/-- The specified lift factors every cone leg. -/
private theorem lift_fac (X : HomotopyCategory (PresheafOfModules.{u} (standardSimplicialRing A B)) (ComplexShape.up ℤ))
    (s : Cone (StructuredArrow.proj (DerivedCategory.Qh.obj X) DerivedCategory.Qh ⋙
      Functor.Homotopy.toDerived (extensionDegreewise A B)))
    (g : StructuredArrow (DerivedCategory.Qh.obj X) DerivedCategory.Qh) :
    lift A B X s ≫ (cone A B X).π.app g = s.π.app g := sorry

/-- The specified lift is the unique factorization. -/
private theorem lift_uniq (X : HomotopyCategory (PresheafOfModules.{u} (standardSimplicialRing A B)) (ComplexShape.up ℤ))
    (s : Cone (StructuredArrow.proj (DerivedCategory.Qh.obj X) DerivedCategory.Qh ⋙
      Functor.Homotopy.toDerived (extensionDegreewise A B)))
    (m : s.pt ⟶ (cone A B X).pt) (hm : ∀ g, m ≫ (cone A B X).π.app g = s.π.app g) :
    m = lift A B X s := sorry

/-- The displayed cone is a limit, with the specified lift. -/
private def isLimit (X : HomotopyCategory (PresheafOfModules.{u} (standardSimplicialRing A B)) (ComplexShape.up ℤ)) :
    IsLimit (cone A B X) where
  lift s := lift A B X s
  fac s g := lift_fac A B X s g
  uniq s m hm := lift_uniq A B X s m hm

/-- The specified pointwise cone and lift give a pointwise derived functor. -/
private theorem pointwiseAt
    (X : HomotopyCategory (PresheafOfModules.{u} (standardSimplicialRing A B))
      (ComplexShape.up ℤ)) :
    (Functor.Homotopy.toDerived (extensionDegreewise A B)).HasPointwiseLeftDerivedFunctorAt
      (HomotopyCategory.quasiIso (PresheafOfModules.{u} (standardSimplicialRing A B))
        (ComplexShape.up ℤ)) X :=
  ((Functor.Homotopy.toDerived (extensionDegreewise A B)).hasPointwiseLeftDerivedFunctorAt_iff
    DerivedCategory.Qh _ X).mpr (HasLimit.mk ⟨cone A B X, isLimit A B X⟩)

end DerivedExtensionModel

/-- Degreewise scalar extension has pointwise left derived functors. -/
instance extensionDegreewise_hasPointwiseLeftDerived :
    (Functor.Homotopy.toDerived (extensionDegreewise A B)).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (PresheafOfModules.{u} (standardSimplicialRing A B)) (ComplexShape.up ℤ)) :=
  fun X ↦ DerivedExtensionModel.pointwiseAt A B X

/-- Degreewise scalar extension admits a total left derived functor. -/
instance extensionDegreewise_hasLeftDerived :
    (Functor.Homotopy.toDerived (extensionDegreewise A B)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (PresheafOfModules.{u} (standardSimplicialRing A B)) (ComplexShape.up ℤ)) :=
  Functor.hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor _ _

/-- Derived extension of scalars along `P_• ⟶ B`. -/
def derivedExtension :
    DerivedCategory (PresheafOfModules.{u} (standardSimplicialRing A B)) ⥤
      DerivedCategory (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) :=
  Functor.LeftDerived.Homotopy.functor (extensionDegreewise A B)

/-- Derived extension of scalars commutes with integer shifts. -/
instance derivedExtension_commShift :
    (derivedExtension A B).CommShift ℤ :=
  Functor.totalLeftDerived_commShift
    (Functor.Homotopy.toDerived (extensionDegreewise A B))
    (HomotopyCategory.quasiIso
      (PresheafOfModules.{u} (standardSimplicialRing A B)) (ComplexShape.up ℤ))
    (DerivedCategory.Qh :
      HomotopyCategory (PresheafOfModules.{u} (standardSimplicialRing A B))
        (ComplexShape.up ℤ) ⥤
        DerivedCategory (PresheafOfModules.{u} (standardSimplicialRing A B)))

end Algebra.CotangentComplex.Atiyah
