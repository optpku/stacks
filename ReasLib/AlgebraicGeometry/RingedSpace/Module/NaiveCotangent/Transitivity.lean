module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent.Transitivity
public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent.Presentation.SourceChange
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.NaiveCotangent.InverseImage
import Mathlib.Tactic.CrossRefAttribute

/-!
# Transitivity for naive cotangent complexes of ringed spaces

This is the ringed-space specialization of naive-cotangent transitivity.  Its public inputs are
only a composable pair of morphisms; inverse images of structure sheaves and module pullback are
kept behind the canonical ringed-space API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.NaiveCotangent

variable {X Y Z : RingedSpace.{u}}

namespace Pullback

/-- The representative of `f^* NL(g)` produced by Mathlib's chosen module-pullback functor. -/
@[stacks 0E1Z "chosen module-pullback representative"]
noncomputable abbrev chosenComplex (f : X ⟶ Y) (g : Y ⟶ Z) :
    CochainComplex X.Modules ℤ :=
  (((RingedSpace.Hom.pullback f).mapHomologicalComplex (up ℤ)).obj
    (RingedSpace.naiveCotangent g))

end Pullback

namespace Tower

/-- The iterated inverse image `f⁻¹(g⁻¹ 𝒪_Z)` on `X`. -/
noncomputable abbrev source (f : X ⟶ Y) (g : Y ⟶ Z) :=
  (TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj
    ((TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj Z.sheaf)

/-- The inverse image `f⁻¹ 𝒪_Y` on `X`. -/
noncomputable abbrev middle (f : X ⟶ Y) :=
  (TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj Y.sheaf

/-- The pulled-back structure map `f⁻¹(g⁻¹ 𝒪_Z) ⟶ f⁻¹ 𝒪_Y`. -/
noncomputable abbrev first (f : X ⟶ Y) (g : Y ⟶ Z) :
    source f g ⟶ middle f :=
  RingedSpace.Hom.StructureSheaf.pullbackMap f g

/-- The inverse-image structure map `f⁻¹ 𝒪_Y ⟶ 𝒪_X`. -/
noncomputable abbrev second (f : X ⟶ Y) : middle f ⟶ X.sheaf :=
  RingedSpace.Hom.inverseImageStructureSheafHomComm f

/-- The composite map `f⁻¹(g⁻¹ 𝒪_Z) ⟶ 𝒪_X`. -/
noncomputable abbrev composite (f : X ⟶ Y) (g : Y ⟶ Z) :
    source f g ⟶ X.sheaf :=
  first f g ≫ second f

/-- The canonical comparison `f⁻¹(g⁻¹ 𝒪_Z) ≅ (f ≫ g)⁻¹ 𝒪_Z`. -/
@[stacks 03D6 "composition of inverse-image coefficient sheaves"]
noncomputable abbrev sourceIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    source f g ≅
      (TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).hom.base).obj Z.sheaf :=
  RingedSpace.Hom.StructureSheaf.compIso f g

end Tower

/-- The normalized pullback `f^* NL(g)`, expressed on `X` through the coefficient tower
`f⁻¹(g⁻¹ 𝒪_Z) ⟶ f⁻¹ 𝒪_Y ⟶ 𝒪_X`.  This explicit representative is the public owner used by
transitivity; `Pullback.chosenComplex` is the compatible abstract-left-adjoint presentation. -/
@[stacks 0E1Z "pullback of a naive cotangent complex"]
noncomputable abbrev pullbackComplex (f : X ⟶ Y) (g : Y ⟶ Z) :
    CochainComplex X.Modules ℤ :=
  SheafOfModules.RingedSite.NaiveCotangent.baseChange
    (C := Opens X) (J := Opens.grothendieckTopology X)
    (Tower.first f g) (Tower.second f)

namespace Pullback

/-- The two-stage representative obtained by inverse image over `f⁻¹ 𝒪_Y`, followed by
extension of scalars to `𝒪_X`. -/
@[stacks 0E1Z "factored module-pullback representative"]
noncomputable abbrev factoredComplex (f : X ⟶ Y) (g : Y ⟶ Z) :
    CochainComplex X.Modules ℤ :=
  (SheafOfModules.RingedSite.extendComplex (Tower.second f)).obj
    (TopCat.Sheaf.NaiveCotangent.InverseImage.source f.hom.base
      (RingedSpace.Hom.inverseImageStructureSheafHomComm g))

/-- The canonical comparison from Mathlib's chosen pullback to the two-stage inverse-image and
extension-of-scalars representative. -/
@[stacks 0E1Z "module-pullback factorization comparison"]
noncomputable def factorizationIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    chosenComplex f g ≅ factoredComplex f g :=
  SheafOfModules.RingedSite.InverseImage.Factorization.complexObjIso
    (J := Opens.grothendieckTopology Y) (K := Opens.grothendieckTopology X)
    (Opens.map f.hom.base) (up ℤ)
    (RingedSpace.Hom.commRingSheafPushforwardMap f)
    (RingedSpace.naiveCotangent g)

/-- Extending the explicit inverse-image comparison identifies the two-stage representative
with the normalized coefficient-tower representative. -/
@[stacks 0E1Z "extended inverse-image comparison"]
noncomputable def comparisonIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    factoredComplex f g ≅ pullbackComplex f g :=
  (SheafOfModules.RingedSite.extendComplex (Tower.second f)).mapIso
    (TopCat.Sheaf.NaiveCotangent.InverseImage.comparisonIso f.hom.base
      (RingedSpace.Hom.inverseImageStructureSheafHomComm g))

/-- The canonical isomorphism from Mathlib's chosen module-pullback representative of
`f^* NL(g)` to its normalized coefficient-tower representative.  It first factors module
pullback as inverse image followed by extension of scalars, then applies the explicit
inverse-image comparison for the naive cotangent complex. -/
@[stacks 0E1Z "chosen pullback comparison isomorphism"]
noncomputable def chosenComplexIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    chosenComplex f g ≅ pullbackComplex f g :=
  factorizationIso f g ≪≫ comparisonIso f g

/-- In degree `n`, the forward pullback-factorization comparison is the corresponding component
of the module-sheaf pullback factorization. -/
theorem factorizationIso_hom_f (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℤ) :
    (factorizationIso f g).hom.f n =
      (SheafOfModules.RingedSite.InverseImage.Factorization.pullbackIso
        (J := Opens.grothendieckTopology Y) (K := Opens.grothendieckTopology X)
        (Opens.map f.hom.base)
        (RingedSpace.Hom.commRingSheafPushforwardMap f)).hom.app
          ((RingedSpace.naiveCotangent g).X n) := sorry

/-- In degree `n`, the inverse pullback-factorization comparison is the corresponding inverse
component of the module-sheaf pullback factorization. -/
theorem factorizationIso_inv_f (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℤ) :
    (factorizationIso f g).inv.f n =
      (SheafOfModules.RingedSite.InverseImage.Factorization.pullbackIso
        (J := Opens.grothendieckTopology Y) (K := Opens.grothendieckTopology X)
        (Opens.map f.hom.base)
        (RingedSpace.Hom.commRingSheafPushforwardMap f)).inv.app
          ((RingedSpace.naiveCotangent g).X n) := sorry

/-- In degree `n`, the extended comparison is extension of the explicit opens-site comparison
component. -/
theorem comparisonIso_hom_f (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℤ) :
    (comparisonIso f g).hom.f n =
      (SheafOfModules.RingedSite.extendAlong (Tower.second f)).map
        ((TopCat.Sheaf.NaiveCotangent.InverseImage.comparisonIso f.hom.base
          (RingedSpace.Hom.inverseImageStructureSheafHomComm g)).hom.f n) := sorry

/-- The forward map of the extended inverse-image comparison is the extension of its canonical
inverse-image comparison. -/
@[stacks 0E1Z "extended inverse-image comparison hom", simp]
theorem comparisonIso_hom (f : X ⟶ Y) (g : Y ⟶ Z) :
    (comparisonIso f g).hom =
      (SheafOfModules.RingedSite.extendComplex (Tower.second f)).map
        ((TopCat.Sheaf.NaiveCotangent.InverseImage.comparisonIso f.hom.base
          (RingedSpace.Hom.inverseImageStructureSheafHomComm g)).hom) := sorry

/-- The inverse of the extended inverse-image comparison is the extension of the inverse-image
comparison inverse. -/
@[stacks 0E1Z "extended inverse-image comparison inverse", simp]
theorem comparisonIso_inv (f : X ⟶ Y) (g : Y ⟶ Z) :
    (comparisonIso f g).inv =
      (SheafOfModules.RingedSite.extendComplex (Tower.second f)).map
        ((TopCat.Sheaf.NaiveCotangent.InverseImage.comparisonIso f.hom.base
          (RingedSpace.Hom.inverseImageStructureSheafHomComm g)).inv) := sorry

/-- The forward map of `chosenComplexIso` is the pullback-factorization comparison followed by
extension of the explicit inverse-image comparison. -/
theorem chosenComplexIso_hom (f : X ⟶ Y) (g : Y ⟶ Z) :
    (chosenComplexIso f g).hom =
      (factorizationIso f g).hom ≫ (comparisonIso f g).hom := sorry

/-- In degree `n`, the forward chosen-pullback comparison is the factorization component
followed by extension of the explicit inverse-image comparison component. -/
theorem chosenComplexIso_hom_f (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℤ) :
    (chosenComplexIso f g).hom.f n =
      (factorizationIso f g).hom.f n ≫ (comparisonIso f g).hom.f n := sorry

/-- In degree `n`, the inverse chosen-pullback comparison first applies the inverse-image
comparison inverse and then the inverse pullback-factorization component. -/
theorem chosenComplexIso_inv_f (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℤ) :
    (chosenComplexIso f g).inv.f n =
      (comparisonIso f g).inv.f n ≫ (factorizationIso f g).inv.f n := sorry

end Pullback

/-- Changing from the iterated inverse-image coefficient sheaf to the inverse image along the
composite gives the naive cotangent complex of `f ≫ g`. -/
@[stacks 0E1Z "composition comparison for naive cotangent complexes"]
noncomputable def compositionIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    SheafOfModules.RingedSite.NaiveCotangent.obj (Tower.source f g)
        (Under.mk (Tower.composite f g)) ≅
      RingedSpace.naiveCotangent (f ≫ g) :=
  SheafOfModules.RingedSite.NaiveCotangent.Presentation.sourceIso
    (Tower.sourceIso f g) (Tower.first f g ≫ Tower.second f)
      (RingedSpace.Hom.inverseImageStructureSheafHomComm (f ≫ g))
        (RingedSpace.Hom.StructureSheaf.compositeMap_eq f g)

/-- The canonical map from the normalized pullback complex to `NL(f ≫ g)`. -/
@[stacks 0E1Z "left map in ringed-space naive-cotangent transitivity"]
noncomputable def left (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullbackComplex f g ⟶ RingedSpace.naiveCotangent (f ≫ g) :=
  SheafOfModules.RingedSite.NaiveCotangent.Presentation.left
      (Tower.first f g) (Tower.second f) ≫
    (compositionIso f g).hom

/-- The canonical comparison `NL(f ≫ g) ⟶ NL(f)`. -/
@[stacks 0E1Z "comparison map in ringed-space naive-cotangent transitivity"]
noncomputable def comparison (f : X ⟶ Y) (g : Y ⟶ Z) :
    RingedSpace.naiveCotangent (f ≫ g) ⟶ RingedSpace.naiveCotangent f :=
  (compositionIso f g).inv ≫
    SheafOfModules.RingedSite.NaiveCotangent.Presentation.comparison
      (Tower.first f g) (Tower.second f)

/-- The composite of the ringed-space transitivity maps is the site-level composite after
transporting the coefficient source. -/
theorem left_comp_comparison (f : X ⟶ Y) (g : Y ⟶ Z) :
    left f g ≫ comparison f g =
      SheafOfModules.RingedSite.NaiveCotangent.Presentation.left
          (Tower.first f g) (Tower.second f) ≫
        SheafOfModules.RingedSite.NaiveCotangent.Presentation.comparison
          (Tower.first f g) (Tower.second f) := sorry

/-- The canonical null-homotopy of the composite of the two ringed-space transitivity maps. -/
@[stacks 0E1Z "ringed-space naive-cotangent transitivity null-homotopy"]
noncomputable def nullHomotopy (f : X ⟶ Y) (g : Y ⟶ Z) :
    Homotopy (left f g ≫ comparison f g) 0 :=
  (Homotopy.ofEq (left_comp_comparison f g)).trans
    (SheafOfModules.RingedSite.NaiveCotangent.Presentation.nullHomotopy
      (Tower.first f g) (Tower.second f))

/-- The canonical map from the normalized pullback complex to the shifted cone of the comparison. -/
@[stacks 0E1Z "ringed-space naive-cotangent transitivity cocone map"]
noncomputable def toCocone (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullbackComplex f g ⟶ CochainComplex.mappingCocone (comparison f g) :=
  CochainComplex.MappingCoconeFactorization.map
    (left f g) (comparison f g) (nullHomotopy f g)

/-- The canonical cocone map projects to the ringed-space left map. -/
@[simp]
theorem toCocone_fst (f : X ⟶ Y) (g : Y ⟶ Z) :
    toCocone f g ≫ CochainComplex.mappingCocone.fst (comparison f g) =
      left f g := sorry

/-- The transitivity datum for composable morphisms `X ⟶ Y ⟶ Z` of ringed spaces. -/
@[stacks 0E1Z "transitivity datum for ringed spaces"]
structure Transitivity (f : X ⟶ Y) (g : Y ⟶ Z) where
  /-- The comparison `NL(X/Z) ⟶ NL(X/Y)`. -/
  comparison : RingedSpace.naiveCotangent (f ≫ g) ⟶ RingedSpace.naiveCotangent f
  /-- The canonical map from `f^* NL(Y/Z)` to the shifted cone of `comparison`. -/
  toCocone : pullbackComplex f g ⟶ CochainComplex.mappingCocone comparison
  /-- The transitivity map is an isomorphism on degree-zero homology. -/
  zeroIsIso : IsIso (HomologicalComplex.homologyMap toCocone 0)
  /-- The transitivity map is an epimorphism on degree-minus-one homology. -/
  negOneEpi : Epi (HomologicalComplex.homologyMap toCocone (-1))

namespace Transitivity

/-- The Jacobi-Zariski six-term homology segment attached to a ringed-space transitivity
datum. -/
@[stacks 0E1Z "naive cotangent six-term sequence for ringed spaces"]
noncomputable def sixTerm {f : X ⟶ Y} {g : Y ⟶ Z} (t : Transitivity f g) :
    ComposableArrows X.Modules 5 :=
  CochainComplex.mappingCocone.sixTerm t.comparison t.toCocone t.zeroIsIso

/-- The Jacobi-Zariski six-term segment attached to a ringed-space transitivity datum is exact. -/
@[stacks 0E1Z "exact naive-cotangent transitivity sequence for ringed spaces"]
theorem sixTerm_exact {f : X ⟶ Y} {g : Y ⟶ Z}
    (t : Transitivity f g) : t.sixTerm.Exact := sorry

/-- The degree-zero comparison `H⁰(NL(f ≫ g)) ⟶ H⁰(NL(f))` is epic. -/
theorem comparison_zero_epi {f : X ⟶ Y} {g : Y ⟶ Z} (t : Transitivity f g) :
    Epi (HomologicalComplex.homologyMap t.comparison 0) := sorry

end Transitivity

/-- Lemma 17.31.7 (0E1Z): the canonical transitivity cocone map is an isomorphism on
degree-zero homology. -/
@[stacks 0E1Z "degree-zero naive-cotangent transitivity for ringed spaces"]
instance toCocone_zero_isIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    IsIso (HomologicalComplex.homologyMap (toCocone f g) 0) := sorry

/-- Lemma 17.31.7 (0E1Z): the canonical transitivity cocone map is epic on
degree-minus-one homology. -/
@[stacks 0E1Z "degree-minus-one naive-cotangent transitivity for ringed spaces"]
instance toCocone_negOne_epi (f : X ⟶ Y) (g : Y ⟶ Z) :
    Epi (HomologicalComplex.homologyMap (toCocone f g) (-1)) := sorry

/-- Lemma 17.31.7 (0E1Z): the canonical transitivity datum for composable morphisms of
ringed spaces. -/
@[stacks 0E1Z "naive cotangent transitivity for ringed spaces"]
noncomputable def transitivity (f : X ⟶ Y) (g : Y ⟶ Z) :
    Transitivity f g where
  comparison := comparison f g
  toCocone := toCocone f g
  zeroIsIso := toCocone_zero_isIso f g
  negOneEpi := toCocone_negOne_epi f g

end AlgebraicGeometry.RingedSpace.NaiveCotangent
