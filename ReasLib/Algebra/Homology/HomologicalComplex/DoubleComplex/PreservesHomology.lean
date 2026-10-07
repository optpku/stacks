module

public import ReasLib.Algebra.Homology.HomologicalComplex.DoubleComplex.Functor
public import ReasLib.Algebra.Homology.HomologicalComplex.DoubleComplex.Row
public import ReasLib.Algebra.Homology.HomologicalComplex.PreservesHomology

/-!
# Homology after applying a functor to a double complex

When a functor preserves homology in one direction of a double complex, the componentwise
comparisons assemble into an isomorphism of complexes in the other direction.  The two
orientations are kept in the parallel namespaces `Map.Row.Homology` and
`Map.Column.Homology`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v₁ v₂ u₁ u₂ w₁ w₂

namespace HomologicalComplex₂

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]
variable {I₁ : Type w₁} {I₂ : Type w₂}
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}

namespace Map.Row.Homology

/-- The component comparison between row homology after mapping and the mapped homology complex
of the original double complex. -/
noncomputable def componentIso
    (K : HomologicalComplex₂ C c₁ c₂) (F : C ⥤ D) [F.Additive]
    (i : I₁) [∀ q : I₂, F.PreservesLeftHomologyOf ((K.flip.X q).sc i)] (q : I₂) :
    ((((F.mapHomologicalComplex₂ c₁ c₂).obj K).flip.X q).homology i) ≅
      ((F.mapHomologicalComplex c₂).obj (K.homology i)).X q :=
  (K.flip.X q).mapHomologyIso F i ≪≫ F.mapIso (K.rowHomologyIso i q)

/-- The mapped row-homology component comparisons commute with the differential in the other
direction. -/
theorem componentIso_comm
    (K : HomologicalComplex₂ C c₁ c₂) (F : C ⥤ D) [F.Additive]
    (i : I₁) [∀ q : I₂, F.PreservesLeftHomologyOf ((K.flip.X q).sc i)]
    (q r : I₂) (hqr : c₂.Rel q r) :
    (componentIso K F i q).hom ≫
        ((F.mapHomologicalComplex c₂).obj (K.homology i)).d q r =
      (((HomologicalComplex.homologyFunctor D c₁ i).mapHomologicalComplex c₂).obj
          ((F.mapHomologicalComplex₂ c₁ c₂).obj K).flip).d q r ≫
        (componentIso K F i r).hom := sorry

/-- Taking row homology after applying a functor agrees with applying the functor to the homology
complex, provided the functor preserves the relevant row homology objects. -/
noncomputable def complexIso
    (K : HomologicalComplex₂ C c₁ c₂) (F : C ⥤ D) [F.Additive]
    (i : I₁) [∀ q : I₂, F.PreservesLeftHomologyOf ((K.flip.X q).sc i)] :
    ((HomologicalComplex.homologyFunctor D c₁ i).mapHomologicalComplex c₂).obj
        ((F.mapHomologicalComplex₂ c₁ c₂).obj K).flip ≅
      (F.mapHomologicalComplex c₂).obj (K.homology i) :=
  HomologicalComplex.Hom.isoOfComponents
    (componentIso K F i)
    (componentIso_comm K F i)

/-- The mapped row-homology complex comparison evaluates to its canonical component
comparison. -/
@[simp]
theorem complexIso_hom_f
    (K : HomologicalComplex₂ C c₁ c₂) (F : C ⥤ D) [F.Additive]
    (i : I₁) [∀ q : I₂, F.PreservesLeftHomologyOf ((K.flip.X q).sc i)] (q : I₂) :
    (complexIso K F i).hom.f q =
      (componentIso K F i q).hom := sorry

end Map.Row.Homology

namespace Map.Column.Homology

/-- The component comparison between column homology after mapping and the mapped homology
object of the original column. -/
noncomputable def componentIso
    (K : HomologicalComplex₂ C c₁ c₂) (F : C ⥤ D) [F.Additive]
    (q : I₂) [∀ p : I₁, F.PreservesLeftHomologyOf ((K.X p).sc q)] (p : I₁) :
    (((F.mapHomologicalComplex₂ c₁ c₂).obj K).X p).homology q ≅
      ((F.mapHomologicalComplex c₁).obj
        (((HomologicalComplex.homologyFunctor C c₂ q).mapHomologicalComplex c₁).obj K)).X p :=
  (K.X p).mapHomologyIso F q

/-- The mapped column-homology component comparisons commute with the differential in the
other direction. -/
theorem componentIso_comm
    (K : HomologicalComplex₂ C c₁ c₂) (F : C ⥤ D) [F.Additive]
    (q : I₂) [∀ p : I₁, F.PreservesLeftHomologyOf ((K.X p).sc q)]
    (p r : I₁) (hpr : c₁.Rel p r) :
    (componentIso K F q p).hom ≫
        ((F.mapHomologicalComplex c₁).obj
          (((HomologicalComplex.homologyFunctor C c₂ q).mapHomologicalComplex c₁).obj K)).d p r =
      (((HomologicalComplex.homologyFunctor D c₂ q).mapHomologicalComplex c₁).obj
          ((F.mapHomologicalComplex₂ c₁ c₂).obj K)).d p r ≫
        (componentIso K F q r).hom := sorry

/-- Taking column homology after applying a functor agrees with applying the functor to the
column-homology complex, provided the functor preserves the relevant column homology objects. -/
noncomputable def complexIso
    (K : HomologicalComplex₂ C c₁ c₂) (F : C ⥤ D) [F.Additive]
    (q : I₂) [∀ p : I₁, F.PreservesLeftHomologyOf ((K.X p).sc q)] :
    ((HomologicalComplex.homologyFunctor D c₂ q).mapHomologicalComplex c₁).obj
        ((F.mapHomologicalComplex₂ c₁ c₂).obj K) ≅
      (F.mapHomologicalComplex c₁).obj
        (((HomologicalComplex.homologyFunctor C c₂ q).mapHomologicalComplex c₁).obj K) :=
  HomologicalComplex.Hom.isoOfComponents
    (componentIso K F q)
    (componentIso_comm K F q)

/-- The mapped column-homology complex comparison evaluates to its canonical component
comparison. -/
@[simp]
theorem complexIso_hom_f
    (K : HomologicalComplex₂ C c₁ c₂) (F : C ⥤ D) [F.Additive]
    (q : I₂) [∀ p : I₁, F.PreservesLeftHomologyOf ((K.X p).sc q)] (p : I₁) :
    (complexIso K F q).hom.f p =
      (componentIso K F q p).hom := sorry

end Map.Column.Homology

end HomologicalComplex₂
