module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Augmentation
public import ReasLib.CategoryTheory.Abelian.Injective.Resolution
public import ReasLib.Algebra.Homology.HomologicalComplex.DoubleComplex.ColumnTransport

/-!
# Functoriality of Cartan--Eilenberg column resolutions

The horizontal differential of a Cartan--Eilenberg double complex transports across the chosen
column comparisons to a morphism of injective resolutions.  This file owns that morphism and its
compatibility with the mapped column-homology comparison.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CochainComplex.CartanEilenbergResolution

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {K : CochainComplex.Plus A}

/-- The morphism between chosen column resolutions induced by a horizontal differential of the
Cartan--Eilenberg double complex. -/
@[stacks 015J "the morphism between chosen column resolutions"]
noncomputable abbrev Column.resolutionMap
    (I : CartanEilenbergResolution K) (p r : ℤ) :
    (I.columnResolution p).cochainComplex ⟶ (I.columnResolution r).cochainComplex :=
  HomologicalComplex₂.Column.Transport.d I.bicomplex
    (fun p => Column.resolutionIso I p) p r

/-- The component of `Column.resolutionMap` is obtained by conjugating the corresponding
horizontal differential by the chosen column comparisons. -/
@[simp]
theorem Column.resolutionMap_f
    (I : CartanEilenbergResolution K) (p r q : ℤ) :
    (Column.resolutionMap I p r).f q =
      (Column.resolutionIso I p).hom.f q ≫ (I.bicomplex.d p r).f q ≫
        (Column.resolutionIso I r).inv.f q := sorry

/-- The chosen column resolutions, equipped with the transported horizontal differentials, form
a double complex. -/
@[stacks 015J "the double complex of chosen column resolutions"]
noncomputable abbrev Column.resolutionBicomplex
    (I : CartanEilenbergResolution K) : HomologicalComplex₂ A (up ℤ) (up ℤ) :=
  HomologicalComplex₂.Column.Transport.bicomplex I.bicomplex
    (fun p => Column.resolutionIso I p)

/-- The column in horizontal degree `p` of `Column.resolutionBicomplex` is the chosen resolution
of the source term in that degree. -/
@[simp]
theorem Column.resolutionBicomplex_X
    (I : CartanEilenbergResolution K) (p : ℤ) :
    (Column.resolutionBicomplex I).X p = (I.columnResolution p).cochainComplex := sorry

/-- The horizontal differential of `Column.resolutionBicomplex` is `Column.resolutionMap`. -/
@[simp]
theorem Column.resolutionBicomplex_d
    (I : CartanEilenbergResolution K) (p r : ℤ) :
    (Column.resolutionBicomplex I).d p r = Column.resolutionMap I p r := sorry

/-- The chosen column comparisons intertwine the transported and original horizontal
differentials. -/
@[reassoc]
theorem Column.resolutionBicomplexIso_hom_d
    (I : CartanEilenbergResolution K) (p r : ℤ) :
    (Column.resolutionIso I p).hom ≫ I.bicomplex.d p r =
      Column.resolutionMap I p r ≫ (Column.resolutionIso I r).hom := sorry

/-- The inverse chosen column comparisons intertwine the original and transported horizontal
differentials. -/
@[reassoc]
theorem Column.resolutionBicomplexIso_inv_d
    (I : CartanEilenbergResolution K) (p r : ℤ) :
    (Column.resolutionIso I p).inv ≫ Column.resolutionMap I p r =
      I.bicomplex.d p r ≫ (Column.resolutionIso I r).inv := sorry

/-- The chosen column comparisons form a commuting square between the transported and original
horizontal differentials. -/
theorem Column.resolutionBicomplexIso_commSq
    (I : CartanEilenbergResolution K) (p r : ℤ) :
    CommSq
      (Column.resolutionMap I p r)
      (Column.resolutionIso I p).hom
      (Column.resolutionIso I r).hom
      (I.bicomplex.d p r) := sorry

/-- The double complex of chosen column resolutions is canonically isomorphic to the original
Cartan--Eilenberg double complex. -/
@[stacks 015J "the chosen column-resolution double-complex comparison"]
noncomputable abbrev Column.resolutionBicomplexIso
    (I : CartanEilenbergResolution K) : Column.resolutionBicomplex I ≅ I.bicomplex :=
  HomologicalComplex₂.Column.Transport.iso I.bicomplex
    (fun p => Column.resolutionIso I p)

/-- Evaluating `Column.resolutionBicomplexIso` at a horizontal degree recovers the chosen column
comparison. -/
@[simp]
theorem Column.resolutionBicomplexIso_app
    (I : CartanEilenbergResolution K) (p : ℤ) :
    HomologicalComplex.Hom.isoApp (Column.resolutionBicomplexIso I) p =
      Column.resolutionIso I p := sorry

/-- The component of `Column.resolutionBicomplexIso` is the chosen comparison for that
column. -/
@[simp]
theorem Column.resolutionBicomplexIso_hom_f
    (I : CartanEilenbergResolution K) (p : ℤ) :
    (Column.resolutionBicomplexIso I).hom.f p = (Column.resolutionIso I p).hom := sorry

/-- The inverse component of `Column.resolutionBicomplexIso` is the inverse chosen comparison for
that column. -/
@[simp]
theorem Column.resolutionBicomplexIso_inv_f
    (I : CartanEilenbergResolution K) (p : ℤ) :
    (Column.resolutionBicomplexIso I).inv.f p = (Column.resolutionIso I p).inv := sorry

/-- The column augmentations are natural with respect to the horizontal differentials. -/
@[reassoc]
theorem Column.Augmentation.naturality
    (I : CartanEilenbergResolution K) (p r : ℤ) :
    (CochainComplex.singleFunctor A 0).map (K.obj.d p r) ≫ Column.Augmentation.map I r =
      Column.Augmentation.map I p ≫ I.bicomplex.d p r := sorry

/-- The column augmentations form a commuting square with every horizontal differential. -/
theorem Column.Augmentation.commSq
    (I : CartanEilenbergResolution K) (p r : ℤ) :
    CommSq
      ((CochainComplex.singleFunctor A 0).map (K.obj.d p r))
      (Column.Augmentation.map I p)
      (Column.Augmentation.map I r)
      (I.bicomplex.d p r) := sorry

/-- The horizontal differential, transported to the chosen columns, is a morphism between the
corresponding injective resolutions of the source terms. -/
@[stacks 015J "the morphism of chosen column resolutions"]
noncomputable def Column.resolutionHom
    (I : CartanEilenbergResolution K) (p r : ℤ) :
    CategoryTheory.InjectiveResolution.Hom
      (I.columnResolution p) (I.columnResolution r) (K.obj.d p r) where
  hom :=
      (InjectiveResolution.Restriction.iso (I.columnResolution p)).inv ≫
      HomologicalComplex.restrictionMap (Column.resolutionMap I p r) embeddingUpNat ≫
        (InjectiveResolution.Restriction.iso (I.columnResolution r)).hom
  ι_f_zero_comp_hom_f_zero := sorry

/-- The native cocomplex map of `Column.resolutionHom` is the restriction of
`Column.resolutionMap`, transported across the canonical restriction comparisons. -/
@[simp]
theorem Column.resolutionHom_hom
    (I : CartanEilenbergResolution K) (p r : ℤ) :
    (Column.resolutionHom I p r).hom =
      (InjectiveResolution.Restriction.iso (I.columnResolution p)).inv ≫
      HomologicalComplex.restrictionMap (Column.resolutionMap I p r) embeddingUpNat ≫
          (InjectiveResolution.Restriction.iso (I.columnResolution r)).hom := sorry

/-- Extending `Column.resolutionHom` back to an integer-indexed cochain map recovers
`Column.resolutionMap`. -/
@[simp]
theorem Column.resolutionHom_hom'
    (I : CartanEilenbergResolution K) (p r : ℤ) :
    (Column.resolutionHom I p r).hom' = Column.resolutionMap I p r := sorry

section Map

variable {B : Type u₂} [Category.{v₂} B] [Preadditive B] [CategoryWithHomology B]

namespace Column.mapResolutionHomologyIso

/-- The column-resolution homology comparisons are natural with respect to the transported
horizontal differential. -/
@[reassoc]
theorem hom_naturality
    (I : CartanEilenbergResolution K) (F : A ⥤ B) [F.Additive]
    (p r q : ℤ) :
    HomologicalComplex.homologyMap
          ((F.mapHomologicalComplex (up ℤ)).map
            (Column.resolutionMap I p r)) q ≫
        (Column.mapResolutionHomologyIso I F r q).hom =
      (Column.mapResolutionHomologyIso I F p q).hom ≫
        HomologicalComplex.homologyMap
          ((F.mapHomologicalComplex (up ℤ)).map (I.bicomplex.d p r)) q := sorry

/-- The column-resolution homology comparisons form a commuting square with every transported
horizontal differential. -/
theorem commSq
    (I : CartanEilenbergResolution K) (F : A ⥤ B) [F.Additive]
    (p r q : ℤ) :
    CommSq
      (f := HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (up ℤ)).map
          (Column.resolutionMap I p r)) q)
      (g := (Column.mapResolutionHomologyIso I F p q).hom)
      (h := (Column.mapResolutionHomologyIso I F r q).hom)
      (i := HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (up ℤ)).map (I.bicomplex.d p r)) q) := sorry

/-- The inverse column-resolution homology comparisons are natural with respect to the
horizontal differential. -/
@[reassoc]
theorem inv_naturality
    (I : CartanEilenbergResolution K) (F : A ⥤ B) [F.Additive]
    (p r q : ℤ) :
    HomologicalComplex.homologyMap
          ((F.mapHomologicalComplex (up ℤ)).map (I.bicomplex.d p r)) q ≫
        (Column.mapResolutionHomologyIso I F r q).inv =
      (Column.mapResolutionHomologyIso I F p q).inv ≫
        HomologicalComplex.homologyMap
          ((F.mapHomologicalComplex (up ℤ)).map
            (Column.resolutionMap I p r)) q := sorry

/-- Conjugating the transported column homology map by the comparison isomorphisms recovers the
original column-homology map. -/
@[reassoc, stacks 015J "source-map computation for column homology comparisons"]
theorem source_map
    (I : CartanEilenbergResolution K) (F : A ⥤ B) [F.Additive]
    (p r q : ℤ) :
    (Column.mapResolutionHomologyIso I F p q).hom ≫
        HomologicalComplex.homologyMap
          ((F.mapHomologicalComplex (up ℤ)).map (I.bicomplex.d p r)) q ≫
      (Column.mapResolutionHomologyIso I F r q).inv =
    HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (up ℤ)).map
        (Column.resolutionMap I p r)) q := sorry

/-- Conjugating the original column-homology map by the inverse comparisons recovers the
transported column map. -/
@[reassoc, stacks 015J "target-map computation for column homology comparisons"]
theorem target_map
    (I : CartanEilenbergResolution K) (F : A ⥤ B) [F.Additive]
    (p r q : ℤ) :
    (Column.mapResolutionHomologyIso I F p q).inv ≫
        HomologicalComplex.homologyMap
          ((F.mapHomologicalComplex (up ℤ)).map
            (Column.resolutionMap I p r)) q ≫
      (Column.mapResolutionHomologyIso I F r q).hom =
    HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (up ℤ)).map (I.bicomplex.d p r)) q := sorry

end Column.mapResolutionHomologyIso

end Map

end CochainComplex.CartanEilenbergResolution
