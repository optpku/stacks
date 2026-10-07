module

public import ReasLib.Algebra.Homology.DerivedCategory.Monoidal.KFlat
public import ReasLib.Algebra.Homology.HomotopyCategory.KFlat.Resolution
public import Mathlib.CategoryTheory.Localization.Predicate

/-!
# K-flat resolutions and the derived category

A selected functorial K-flat resolution gives a concrete functor from the homotopy category to
the derived category.  Its comparison with `DerivedCategory.Qh` is explicit natural-transformation
data; the comparison isomorphism below selects its components directly from the ambient
localization, leaving only naturality as proof data.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory.KFlat

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
variable [MonoidalCategory C] [MonoidalPreadditive C]

/-- Stacks 0FPB: the derived-category realization of a selected functorial K-flat resolution. -/
@[stacks 0FPB "derived realization of a functorial K-flat resolution"]
noncomputable abbrev resolvedLocalization
    (P : HomotopyCategory.KFlat.ResolutionFunctor C) :
    HomotopyCategory C (up ℤ) ⥤ DerivedCategory C :=
  P.toFunctor ⋙ localizationFunctor (C := C)

/-- Stacks 0FPB: the natural comparison from the derived realization of a selected K-flat
resolution to the canonical homotopy-to-derived localization functor. -/
@[stacks 0FPB "functorial K-flat resolution comparison"]
noncomputable def resolutionCounit
    (P : HomotopyCategory.KFlat.ResolutionFunctor C) :
    resolvedLocalization P ⟶
      (DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C) :=
  Functor.whiskerRight P.counit
    (DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C)

/-- The component of the derived comparison associated to a functorial K-flat resolution. -/
@[stacks 0FPB "functorial K-flat resolution comparison component"]
noncomputable abbrev resolutionCounitApp
    (P : HomotopyCategory.KFlat.ResolutionFunctor C)
    (K : HomotopyCategory C (up ℤ)) :
    (resolvedLocalization P).obj K ⟶
      (DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C).obj K :=
  (resolutionCounit P).app K

/-- Every component of the derived comparison associated to a functorial K-flat resolution is an
isomorphism. Registering this canonical fact lets downstream constructions use typeclass search
instead of rebuilding a proof-local `IsIso`. -/
@[stacks 0FPB "functorial K-flat resolution comparison is invertible"]
instance resolutionCounit_isIso
    (P : HomotopyCategory.KFlat.ResolutionFunctor C)
    (K : HomotopyCategory C (up ℤ)) :
    IsIso (resolutionCounitApp P K) := sorry

/-- Stacks 0FPB: the object-level comparison for a selected K-flat resolution.  This owner exposes
the localized morphism directly and does not depend on the naturality proof packaged in
`resolutionIso`. -/
@[stacks 0FPB "objectwise K-flat resolution isomorphism"]
noncomputable def resolutionObjIso
    (P : HomotopyCategory.KFlat.ResolutionFunctor C)
    (K : HomotopyCategory C (up ℤ)) :
    (resolvedLocalization P).obj K ≅
      (DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C).obj K :=
  Localization.isoOfHom
    (DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C)
    (HomotopyCategory.quasiIso C (up ℤ)) (P.counit.app K) (P.quasiIso_app K)

/-- Stacks 0FPB: expose the underlying localized morphism of the object-level comparison. -/
@[simp, stacks 0FPB "objectwise K-flat resolution counit"]
theorem resolutionObjIso_hom
    (P : HomotopyCategory.KFlat.ResolutionFunctor C)
    (K : HomotopyCategory C (up ℤ)) :
    (resolutionObjIso P K).hom = resolutionCounitApp P K := sorry

/-- Stacks 0FPB: the selected K-flat resolution is naturally isomorphic to the canonical derived
localization.  Each component is the localization isomorphism induced by the concrete
quasi-isomorphism in `P.counit`; only naturality remains proof debt. -/
@[stacks 0FPB "functorial K-flat resolution isomorphism"]
noncomputable def resolutionIso
    (P : HomotopyCategory.KFlat.ResolutionFunctor C) :
    resolvedLocalization P ≅
      (DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C) :=
  NatIso.ofComponents
    (fun K => resolutionObjIso P K)
    (fun f => sorry)

/-- Stacks 0FPB: the component of `resolutionIso` has the selected resolution counit as its
underlying localized morphism. -/
@[stacks 0FPB "resolution isomorphism component"]
theorem resolutionIso_hom_app
    (P : HomotopyCategory.KFlat.ResolutionFunctor C)
    (K : HomotopyCategory C (up ℤ)) :
    (resolutionIso P).hom.app K = resolutionCounitApp P K := sorry

/-- Stacks 0FPB: expose the inverse component of the selected K-flat resolution comparison. -/
@[stacks 0FPB "inverse resolution isomorphism component"]
noncomputable abbrev resolutionIsoInvApp
    (P : HomotopyCategory.KFlat.ResolutionFunctor C)
    (K : HomotopyCategory C (up ℤ)) :
    (DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C).obj K ⟶
      (resolvedLocalization P).obj K :=
  (resolutionIso P).inv.app K

/-- The derived realization of a functorial K-flat resolution and the canonical localization
functor are isomorphic, without selecting a proof-dependent natural isomorphism. -/
@[stacks 0FPB "functorial K-flat derived realization uniqueness"]
theorem resolvedLocalization_isIsomorphic
    (P : HomotopyCategory.KFlat.ResolutionFunctor C) :
    IsIsomorphic (resolvedLocalization P)
      (DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C) := sorry

end CategoryTheory.DerivedCategory.KFlat
