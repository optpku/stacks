module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.UniversalMap

/-!
# Morphisms of the affine-glued relative spectra

An algebra map acts on every affine chart by the actual contravariant `Spec`
map. A colimit descent glues these maps to a morphism of the constructed schemes.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {A B C : S.QcAlgebraUnder}

/-- The compatible maps on the section spectra of an algebra morphism. -/
def relativeSpectrumMapCocone (α : A ⟶ B) :
    Cocone (relativeSpectrumNativeGluingData B).functor where
  pt := (relativeSpectrumRealization A).Y
  ι :=
    { app := fun (U : S.affineOpens) ↦
        Spec.map ((InducedCategory.Hom.hom α.hom.right).app (op (U : S.Opens))) ≫
          colimit.ι (relativeSpectrumNativeGluingData A).functor U
      naturality := sorry }

/-- The morphism of constructed relative spectra induced contravariantly by an algebra map. -/
def relativeSpectrumMap (α : A ⟶ B) :
    (relativeSpectrumOver B).scheme ⟶ (relativeSpectrumOver A).scheme :=
  colimit.desc _ (relativeSpectrumMapCocone α)

/-- On each affine chart the global morphism is the `Spec` map of the actual section-ring map. -/
theorem relativeSpectrumMap_ι (α : A ⟶ B) (U : S.affineOpens) :
    colimit.ι (relativeSpectrumNativeGluingData B).functor U ≫ relativeSpectrumMap α =
      Spec.map ((InducedCategory.Hom.hom α.hom.right).app (op (U : S.Opens))) ≫
        colimit.ι (relativeSpectrumNativeGluingData A).functor U := sorry

/-- The glued algebra-induced map preserves the specified structural morphism to the base. -/
theorem relativeSpectrumMap_toBase (α : A ⟶ B) :
    relativeSpectrumMap α ≫ (relativeSpectrumOver A).π = (relativeSpectrumOver B).π := sorry

/-- The spectrum construction preserves identity maps of algebras. -/
theorem relativeSpectrumMap_id (A : S.QcAlgebraUnder) :
    relativeSpectrumMap (𝟙 A) = 𝟙 (relativeSpectrumOver A).scheme := sorry

/-- Composition of algebra maps reverses the order of the glued spectrum morphisms. -/
theorem relativeSpectrumMap_comp (α : A ⟶ B) (β : B ⟶ C) :
    relativeSpectrumMap (α ≫ β) = relativeSpectrumMap β ≫ relativeSpectrumMap α := sorry

/-- The source algebra category acts contravariantly by the constructed schemes and maps. -/
def relativeSpectrumSchemeFunctor (S : Scheme.{u}) : S.QcAlgebraUnderᵒᵖ ⥤ Scheme.{u} where
  obj A := (relativeSpectrumOver A.unop).scheme
  map α := relativeSpectrumMap α.unop
  map_id := sorry
  map_comp := sorry

end AlgebraicGeometry.Scheme
