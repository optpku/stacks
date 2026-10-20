/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.NaiveCotangent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Differentials.Conormal.Stalk
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Canonical
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Reindex
public import ReasLib.RingTheory.Extension.Section
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Category.Ring.Under.Basic

/-!
# Stalks of naive cotangent complexes

This file compares the ordinary topological stalk of the sheaf-level naive cotangent complex with
the canonical algebraic naive cotangent complex of the induced morphism on stalk rings.  It uses
`SheafOfModules.stalkFunctorOfCommRing` directly, so the API does not pass through a separately
chosen presentation of the corresponding point of the opens site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf Limits TopCat TopologicalSpace ComplexShape
open SheafOfModules.RingedSite
open scoped NaiveCotangent

noncomputable section

universe u

namespace TopCat.Sheaf.NaiveCotangent

variable {X : TopCat.{u}} {O₁ O₂ : X.Sheaf CommRingCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology X) CommRingCat.{u}]
variable [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology X).HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The ordinary stalkwise realization of the sheaf-level naive cotangent complex. -/
abbrev stalk (φ : O₁ ⟶ O₂) (x : X) :
    CochainComplex (ModuleCat (O₂.presheaf.stalk x)) ℤ :=
  (((SheafOfModules.stalkFunctorOfCommRing O₂ x).mapHomologicalComplex (up ℤ)).obj
    (SheafOfModules.RingedSite.NaiveCotangent.obj O₁ (Under.mk φ)))

/-- The algebraic naive cotangent complex of the induced morphism on stalk rings, transported to
cohomological degrees `-1` and `0`. -/
abbrev algebraicStalk (φ : O₁ ⟶ O₂) (x : X) :
    CochainComplex (ModuleCat (O₂.presheaf.stalk x)) ℤ :=
  ((CommRingCat.Hom.naiveCotangent
    ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map φ.hom)).extend embeddingDownNat)

omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
  [(Opens.grothendieckTopology X).HasSheafCompose
    (CategoryTheory.forget CommRingCat.{u})] in
/-- Degree `-1` of the stalkwise complex is the stalk of the conormal source of the canonical
presentation. -/
theorem stalk_X_negOne (φ : O₁ ⟶ O₂) (x : X) :
    (stalk φ x).X (-1) =
      (SheafOfModules.stalkFunctorOfCommRing O₂ x).obj
        (conormalSource (FreeAlgebra.Presentation.map O₁ (Under.mk φ))) := sorry

namespace PresentationStalk

/-- The sheaf-theoretic free-algebra presentation after taking stalks, bundled under the source
stalk ring. -/
noncomputable abbrev algebra
    (φ : O₁ ⟶ O₂) (x : X) : Under (O₁.presheaf.stalk x) :=
  TopCat.Sheaf.FreeAlgebra.Stalk.sheaf O₁
    (FreeAlgebra.Presentation.generators (Under.mk φ)) x

/-- The target stalk ring, bundled under the source stalk ring. -/
noncomputable abbrev target
    (φ : O₁ ⟶ O₂) (x : X) : Under (O₁.presheaf.stalk x) :=
  Under.mk ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map φ.hom)

/-- The stalk of the sheaf of generators in the canonical free-algebra presentation. -/
@[stacks 0D09 "stalkwise generator type"]
noncomputable abbrev generatorStalk (φ : O₁ ⟶ O₂) (x : X) : Type u :=
  (TopCat.Sheaf.presheaf
    (FreeAlgebra.Presentation.generators (Under.mk φ))).stalk x

/-- Taking stalks of the canonical free-algebra evaluation respects the coefficient map. -/
theorem evaluation_base (φ : O₁ ⟶ O₂) (x : X) :
    (algebra φ x).hom ≫
        (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
          (FreeAlgebra.Presentation.map O₁ (Under.mk φ)).hom =
      (target φ x).hom := sorry

/-- The evaluation from the free-algebra presentation stalk to the target stalk ring. -/
@[stacks 0D09 "stalkwise free-algebra evaluation"]
noncomputable def evaluation (φ : O₁ ⟶ O₂) (x : X) :
    algebra φ x ⟶ target φ x :=
  Under.homMk
    ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
      (FreeAlgebra.Presentation.map O₁ (Under.mk φ)).hom)
    (evaluation_base φ x)

/-- The stalk of the underlying generator sheaf is canonically equivalent to the carrier of the
target stalk ring. -/
@[stacks 0D09 "stalkwise generator equivalence"]
noncomputable def generatorEquiv (φ : O₁ ⟶ O₂) (x : X) :
    generatorStalk φ x ≃ (target φ x).right :=
  (TopCat.Presheaf.stalkCompIso x (CategoryTheory.forget CommRingCat.{u})
    O₂.presheaf).symm.toEquiv

/-- The explicit section of the stalkwise free-algebra evaluation, obtained from the universal
free-algebra generator and the canonical stalk comparison. -/
@[stacks 0D09 "explicit section of the stalkwise free-algebra evaluation"]
noncomputable def extensionSection (φ : O₁ ⟶ O₂) (x : X) :
    (target φ x).right → (algebra φ x).right := fun s ↦
  TopCat.Sheaf.FreeAlgebra.Stalk.comparison O₁
    (FreeAlgebra.Presentation.generators (Under.mk φ)) x
      (TopCat.Sheaf.FreeAlgebra.Stalk.generator O₁
        (FreeAlgebra.Presentation.generators (Under.mk φ)) x
          ((generatorEquiv φ x).symm s))

/-- Evaluating the explicit polynomial-variable section recovers the target-stalk element. -/
theorem extensionSection_spec (φ : O₁ ⟶ O₂) (x : X) (s : (target φ x).right) :
    CommRingCat.toAlgHom (evaluation φ x) (extensionSection φ x s) = s := sorry

/-- The stalkwise canonical free-algebra evaluation is surjective. -/
theorem evaluation_surjective (φ : O₁ ⟶ O₂) (x : X) :
    Function.Surjective (CommRingCat.toAlgHom (evaluation φ x)) := sorry

/-- The algebra extension defined by the stalkwise canonical free-algebra presentation. -/
@[stacks 0D09 "stalkwise canonical algebra extension"]
noncomputable def extension (φ : O₁ ⟶ O₂) (x : X) :
    Algebra.Extension (O₁.presheaf.stalk x) (target φ x).right :=
  Algebra.Extension.ofSection (CommRingCat.toAlgHom (evaluation φ x))
    (extensionSection φ x) (extensionSection_spec φ x)

/-- The polynomial presentation obtained by reindexing the self-presentation along the stalkwise
generator equivalence. -/
@[stacks 0D09 "reindexed stalk-ring presentation"]
noncomputable def generators (φ : O₁ ⟶ O₂) (x : X) :
    Algebra.Generators (O₁.presheaf.stalk x) (target φ x).right
      (generatorStalk φ x) :=
  (Algebra.Generators.self (O₁.presheaf.stalk x) (target φ x).right).reindex
    (generatorEquiv φ x)

/-- The polynomial identification of the free-algebra stalk preserves evaluation at the target
stalk ring. -/
theorem polynomialIso_evaluation (φ : O₁ ⟶ O₂) (x : X)
    (p : (extension φ x).Ring) :
    algebraMap (generators φ x).Ring (target φ x).right
        ((TopCat.Sheaf.FreeAlgebra.Stalk.sheafPolynomialIso O₁
          (FreeAlgebra.Presentation.generators (Under.mk φ)) x).hom.right p) =
      algebraMap (extension φ x).Ring (target φ x).right p := sorry

/-- The polynomial identification of the free-algebra stalk preserves the coefficient map. -/
theorem polynomialIso_base (φ : O₁ ⟶ O₂) (x : X)
    (r : O₁.presheaf.stalk x) :
    (TopCat.Sheaf.FreeAlgebra.Stalk.sheafPolynomialIso O₁
        (FreeAlgebra.Presentation.generators (Under.mk φ)) x).hom.right
        (algebraMap (O₁.presheaf.stalk x) (extension φ x).Ring r) =
      algebraMap (O₁.presheaf.stalk x) (generators φ x).Ring r := sorry

/-- The extension morphism induced by the polynomial identification of the free-algebra stalk. -/
@[stacks 0D09 "free-algebra stalk polynomial extension morphism"]
noncomputable def extensionToGenerators (φ : O₁ ⟶ O₂) (x : X) :
    (extension φ x).Hom (generators φ x).toExtension where
  toRingHom :=
    (TopCat.Sheaf.FreeAlgebra.Stalk.sheafPolynomialIso O₁
      (FreeAlgebra.Presentation.generators (Under.mk φ)) x).hom.right.hom
  toRingHom_algebraMap := polynomialIso_base φ x
  algebraMap_toRingHom := polynomialIso_evaluation φ x

/-- The inverse polynomial identification of the free-algebra stalk preserves evaluation at the
target stalk ring. -/
theorem polynomialIso_inv_evaluation (φ : O₁ ⟶ O₂) (x : X)
    (p : (generators φ x).Ring) :
    algebraMap (extension φ x).Ring (target φ x).right
        ((TopCat.Sheaf.FreeAlgebra.Stalk.sheafPolynomialIso O₁
          (FreeAlgebra.Presentation.generators (Under.mk φ)) x).inv.right p) =
      algebraMap (generators φ x).Ring (target φ x).right p := sorry

/-- The inverse polynomial identification of the free-algebra stalk preserves the coefficient
map. -/
theorem polynomialIso_inv_base (φ : O₁ ⟶ O₂) (x : X)
    (r : O₁.presheaf.stalk x) :
    (TopCat.Sheaf.FreeAlgebra.Stalk.sheafPolynomialIso O₁
        (FreeAlgebra.Presentation.generators (Under.mk φ)) x).inv.right
        (algebraMap (O₁.presheaf.stalk x) (generators φ x).Ring r) =
      algebraMap (O₁.presheaf.stalk x) (extension φ x).Ring r := sorry

/-- The inverse extension morphism induced by the polynomial identification of the free-algebra
stalk. -/
@[stacks 0D09 "inverse free-algebra stalk polynomial extension morphism"]
noncomputable def generatorsToExtension (φ : O₁ ⟶ O₂) (x : X) :
    (generators φ x).toExtension.Hom (extension φ x) where
  toRingHom :=
    (TopCat.Sheaf.FreeAlgebra.Stalk.sheafPolynomialIso O₁
      (FreeAlgebra.Presentation.generators (Under.mk φ)) x).inv.right.hom
  toRingHom_algebraMap := polynomialIso_inv_base φ x
  algebraMap_toRingHom := polynomialIso_inv_evaluation φ x

/-- The inverse polynomial extension morphism composed with the forward morphism is the
identity on the stalkwise presentation extension. -/
theorem toGenerators_inv_comp (φ : O₁ ⟶ O₂) (x : X) :
    (generatorsToExtension φ x).comp (extensionToGenerators φ x) =
      Algebra.Extension.Hom.id (extension φ x) := sorry

/-- The forward polynomial extension morphism composed with the inverse morphism is the
identity on the reindexed polynomial presentation. -/
theorem toGenerators_comp_inv (φ : O₁ ⟶ O₂) (x : X) :
    (extensionToGenerators φ x).comp (generatorsToExtension φ x) =
      Algebra.Extension.Hom.id (generators φ x).toExtension := sorry

/-- The stalkwise free-algebra presentation extension and its polynomial model have canonically
isomorphic naive cotangent complexes. -/
@[stacks 0D09 "free-algebra stalk polynomial complex identification"]
noncomputable def extensionComplexIso (φ : O₁ ⟶ O₂) (x : X) :
    Algebra.Extension.NaiveCotangent.complex (extension φ x) ≅
      Algebra.Extension.NaiveCotangent.complex (generators φ x).toExtension :=
  Algebra.Extension.NaiveCotangent.isoOfHom (extensionToGenerators φ x)
    (generatorsToExtension φ x)
    (toGenerators_inv_comp φ x) (toGenerators_comp_inv φ x)

/-- The scalar-extended kernel-cotangent module of the canonical presentation after taking
stalks. -/
abbrev conormal (φ : O₁ ⟶ O₂) (x : X) :
    ModuleCat (O₂.presheaf.stalk x) :=
  TopCat.Sheaf.Conormal.Stalk.extendedAlgebraic
    (FreeAlgebra.Presentation.map O₁ (Under.mk φ)) x

/-- The degree `-1` component of the mapped two-term complex is definitionally the stalk of its
conormal source. -/
noncomputable def negOneComponentIso (φ : O₁ ⟶ O₂) (x : X) :
    (stalk φ x).X (-1) ≅
      (SheafOfModules.stalkFunctorOfCommRing O₂ x).obj
        (conormalSource (FreeAlgebra.Presentation.map O₁ (Under.mk φ))) :=
  Iso.refl _

omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
  [(Opens.grothendieckTopology X).HasSheafCompose
    (CategoryTheory.forget CommRingCat.{u})] in
/-- The canonical isomorphism from degree `-1` of the sheaf-level stalk to the algebraic
conormal term of the stalkwise canonical presentation. -/
@[stacks 0D09 "degree -1 conormal stalk identification",
  stacks 08UO "degree -1 component"]
noncomputable def negOneIso (φ : O₁ ⟶ O₂) (x : X) :
    (stalk φ x).X (-1) ≅ conormal φ x :=
  negOneComponentIso φ x ≪≫
    TopCat.Sheaf.Conormal.Stalk.sheafStalkIso
      (FreeAlgebra.Presentation.map O₁ (Under.mk φ)) x

omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
  [(Opens.grothendieckTopology X).HasSheafCompose
    (CategoryTheory.forget CommRingCat.{u})] in
/-- The forward map of `negOneIso` is the conormal stalk comparison after the canonical
identification of the degree `-1` term. -/
@[stacks 0D09 "degree -1 conormal stalk identification hom",
  stacks 08UO "degree -1 component hom", simp]
theorem negOneIso_hom (φ : O₁ ⟶ O₂) (x : X) :
    (negOneIso φ x).hom =
      (negOneComponentIso φ x).hom ≫
        TopCat.Sheaf.Conormal.Stalk.sheafComparisonInv
          (FreeAlgebra.Presentation.map O₁ (Under.mk φ)) x ≫
        TopCat.Sheaf.Conormal.Stalk.algebraicComparison
          (FreeAlgebra.Presentation.map O₁ (Under.mk φ)) x := sorry

omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
  [(Opens.grothendieckTopology X).HasSheafCompose
    (CategoryTheory.forget CommRingCat.{u})] in
/-- The inverse map of `negOneIso` applies the explicit algebraic and sheaf conormal
comparisons before the canonical degree identification. -/
@[stacks 0D09 "degree -1 conormal stalk identification inverse",
  stacks 08UO "degree -1 component inverse", simp]
theorem negOneIso_inv (φ : O₁ ⟶ O₂) (x : X) :
    (negOneIso φ x).inv =
      TopCat.Sheaf.Conormal.Stalk.algebraicComparisonInv
          (FreeAlgebra.Presentation.map O₁ (Under.mk φ)) x ≫
        TopCat.Sheaf.Conormal.Stalk.sheafComparison
          (FreeAlgebra.Presentation.map O₁ (Under.mk φ)) x ≫
        (negOneComponentIso φ x).inv := sorry

end PresentationStalk

omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
  [(Opens.grothendieckTopology X).HasSheafCompose
    (CategoryTheory.forget CommRingCat.{u})] in
/-- Degree `0` of the stalkwise complex is the stalk of the tensor term of the canonical
presentation. -/
theorem stalk_X_zero (φ : O₁ ⟶ O₂) (x : X) :
    (stalk φ x).X 0 =
      (SheafOfModules.stalkFunctorOfCommRing O₂ x).obj
        (conormalTensorTerm (FreeAlgebra.Presentation.base O₁ (Under.mk φ))
          (FreeAlgebra.Presentation.map O₁ (Under.mk φ))) := sorry

namespace PresentationStalk

/-- The scalar extension of stalk-ring differentials in the canonical presentation. -/
abbrev differentials (φ : O₁ ⟶ O₂) (x : X) :
    ModuleCat (O₂.presheaf.stalk x) :=
  TopCat.Sheaf.Conormal.Stalk.tensorAlgebraic
    (FreeAlgebra.Presentation.base O₁ (Under.mk φ))
      (FreeAlgebra.Presentation.map O₁ (Under.mk φ)) x

/-- The degree `0` component of the mapped two-term complex is definitionally the stalk of its
relative-differentials tensor term. -/
noncomputable def zeroComponentIso (φ : O₁ ⟶ O₂) (x : X) :
    (stalk φ x).X 0 ≅
      (SheafOfModules.stalkFunctorOfCommRing O₂ x).obj
        (conormalTensorTerm (FreeAlgebra.Presentation.base O₁ (Under.mk φ))
          (FreeAlgebra.Presentation.map O₁ (Under.mk φ))) :=
  Iso.refl _

omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
  [(Opens.grothendieckTopology X).HasSheafCompose
    (CategoryTheory.forget CommRingCat.{u})] in
/-- The canonical isomorphism from degree `0` of the sheaf-level stalk to the algebraic
relative-differentials term of the stalkwise canonical presentation. -/
@[stacks 0D09 "degree 0 differentials stalk identification",
  stacks 08UO "degree 0 component"]
noncomputable def zeroIso (φ : O₁ ⟶ O₂) (x : X) :
    (stalk φ x).X 0 ≅ differentials φ x :=
  zeroComponentIso φ x ≪≫
    TopCat.Sheaf.Conormal.Stalk.tensorStalkIso
      (FreeAlgebra.Presentation.base O₁ (Under.mk φ))
      (FreeAlgebra.Presentation.map O₁ (Under.mk φ)) x

omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
  [(Opens.grothendieckTopology X).HasSheafCompose
    (CategoryTheory.forget CommRingCat.{u})] in
/-- The forward map of `zeroIso` is the differentials stalk comparison after the canonical
identification of the degree `0` term. -/
@[stacks 0D09 "degree 0 differentials stalk identification hom",
  stacks 08UO "degree 0 component hom", simp]
theorem zeroIso_hom (φ : O₁ ⟶ O₂) (x : X) :
    (zeroIso φ x).hom =
      (zeroComponentIso φ x).hom ≫
        TopCat.Sheaf.Conormal.Stalk.tensorComparisonInv
          (FreeAlgebra.Presentation.base O₁ (Under.mk φ))
          (FreeAlgebra.Presentation.map O₁ (Under.mk φ)) x := sorry

omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
  [(Opens.grothendieckTopology X).HasSheafCompose
    (CategoryTheory.forget CommRingCat.{u})] in
/-- The inverse map of `zeroIso` applies the explicit base-changed differentials comparison
before the canonical degree identification. -/
@[stacks 0D09 "degree 0 differentials stalk identification inverse",
  stacks 08UO "degree 0 component inverse", simp]
theorem zeroIso_inv (φ : O₁ ⟶ O₂) (x : X) :
    (zeroIso φ x).inv =
      TopCat.Sheaf.Conormal.Stalk.tensorComparison
          (FreeAlgebra.Presentation.base O₁ (Under.mk φ))
          (FreeAlgebra.Presentation.map O₁ (Under.mk φ)) x ≫
        (zeroComponentIso φ x).inv := sorry

/-- The presentation conormal module is canonically the conormal module attached to the
stalkwise algebra extension. -/
noncomputable def conormalExtensionIso (φ : O₁ ⟶ O₂) (x : X) :
    conormal φ x ≅
      ModuleCat.of (target φ x).right
        (Algebra.Extension.NaiveCotangent.Lift (extension φ x)) :=
  Iso.refl _ ≪≫
    Algebra.Extension.NaiveCotangent.cotangentBaseChangeIso (extension φ x)

/-- The presentation differentials module is definitionally the cotangent-space term attached
to the stalkwise algebra extension. -/
noncomputable def differentialsExtensionIso (φ : O₁ ⟶ O₂) (x : X) :
    differentials φ x ≅
      ModuleCat.of (target φ x).right (extension φ x).CotangentSpace :=
  Iso.refl _

/-- Degree `-1` of the stalkwise complex, identified with degree `1` of the presentation
extension's homological naive cotangent complex. -/
@[stacks 0D09 "degree -1 presentation-extension component"]
noncomputable def negOneExtensionIso (φ : O₁ ⟶ O₂) (x : X) :
    (stalk φ x).X (-1) ≅
      (Algebra.Extension.NaiveCotangent.complex (extension φ x)).X 1 :=
  negOneIso φ x ≪≫
    conormalExtensionIso φ x ≪≫
    (Algebra.Extension.NaiveCotangent.componentOneIso (extension φ x)).symm

/-- Degree `0` of the stalkwise complex, identified with degree `0` of the presentation
extension's homological naive cotangent complex. -/
@[stacks 0D09 "degree 0 presentation-extension component"]
noncomputable def zeroExtensionIso (φ : O₁ ⟶ O₂) (x : X) :
    (stalk φ x).X 0 ≅
      (Algebra.Extension.NaiveCotangent.complex (extension φ x)).X 0 :=
  zeroIso φ x ≪≫
    differentialsExtensionIso φ x ≪≫
    (Algebra.Extension.NaiveCotangent.componentZeroIso (extension φ x)).symm

end PresentationStalk

/-- The presentation-extension naive cotangent complex transported to cohomological degrees
`-1` and `0`. -/
noncomputable abbrev presentationStalk (φ : O₁ ⟶ O₂) (x : X) :
    CochainComplex (ModuleCat (PresentationStalk.target φ x).right) ℤ :=
  (Algebra.Extension.NaiveCotangent.complex
    (PresentationStalk.extension φ x)).extend embeddingDownNat

/-- Away from degrees `-1` and `0`, the stalkwise naive cotangent complex has zero
components. -/
theorem stalk_component_isZero (φ : O₁ ⟶ O₂) (x : X) (i : ℤ)
    (hneg : i ≠ -1) (hzero : i ≠ 0) : IsZero ((stalk φ x).X i) := sorry

/-- Away from degrees `-1` and `0`, the transported presentation-extension complex has zero
components. -/
theorem presentationStalk_component_isZero (φ : O₁ ⟶ O₂) (x : X) (i : ℤ)
    (hneg : i ≠ -1) (hzero : i ≠ 0) : IsZero ((presentationStalk φ x).X i) := sorry

/-- The componentwise canonical comparison from the stalkwise complex to the transported
presentation-extension complex. -/
@[stacks 0D09 "componentwise stalk presentation comparison"]
noncomputable def presentationComponentIso (φ : O₁ ⟶ O₂) (x : X) (i : ℤ) :
    (stalk φ x).X i ≅ (presentationStalk φ x).X i :=
  if hneg : i = -1 then
    eqToIso (congrArg (fun j ↦ (stalk φ x).X j) hneg) ≪≫
      PresentationStalk.negOneExtensionIso φ x ≪≫
      ((Algebra.Extension.NaiveCotangent.complex
        (PresentationStalk.extension φ x)).extendXIso embeddingDownNat rfl).symm ≪≫
      eqToIso (congrArg (fun j ↦ (presentationStalk φ x).X j) hneg).symm
  else if hzero : i = 0 then
    eqToIso (congrArg (fun j ↦ (stalk φ x).X j) hzero) ≪≫
      PresentationStalk.zeroExtensionIso φ x ≪≫
      ((Algebra.Extension.NaiveCotangent.complex
        (PresentationStalk.extension φ x)).extendXIso embeddingDownNat rfl).symm ≪≫
      eqToIso (congrArg (fun j ↦ (presentationStalk φ x).X j) hzero).symm
  else
    (stalk_component_isZero φ x i hneg hzero).isoZero ≪≫
      (presentationStalk_component_isZero φ x i hneg hzero).isoZero.symm

/-- The componentwise stalk-presentation comparison commutes with every differential. -/
theorem presentationComponentIso_comm (φ : O₁ ⟶ O₂) (x : X) :
    ∀ i j (_ : (up ℤ).Rel i j),
      (presentationComponentIso φ x i).hom ≫ (presentationStalk φ x).d i j =
        (stalk φ x).d i j ≫ (presentationComponentIso φ x j).hom := sorry

/-- The stalkwise naive cotangent complex is canonically isomorphic to the transported complex
of its stalkwise free-algebra presentation. -/
@[stacks 0D09 "stalkwise presentation complex identification"]
noncomputable def presentationStalkIso (φ : O₁ ⟶ O₂) (x : X) :
    stalk φ x ≅ presentationStalk φ x :=
  HomologicalComplex.Hom.isoOfComponents (presentationComponentIso φ x)
    (presentationComponentIso_comm φ x)

/-- The polynomial identification of the stalkwise presentation, transported to cohomological
degrees `-1` and `0`. -/
@[stacks 0D09 "polynomial presentation complex identification"]
noncomputable def polynomialStalkIso (φ : O₁ ⟶ O₂) (x : X) :
    presentationStalk φ x ≅
      (Algebra.Extension.NaiveCotangent.complex
        (PresentationStalk.generators φ x).toExtension).extend embeddingDownNat :=
  (embeddingDownNat.extendFunctor
    (ModuleCat (PresentationStalk.target φ x).right)).mapIso
    (PresentationStalk.extensionComplexIso φ x)

/-- Reindexing the stalkwise generator type to the target stalk ring, transported to
cohomological degrees `-1` and `0`. -/
@[stacks 0D09 "stalk-generator reindexing complex identification"]
noncomputable def reindexStalkIso (φ : O₁ ⟶ O₂) (x : X) :
    (Algebra.Extension.NaiveCotangent.complex
        (PresentationStalk.generators φ x).toExtension).extend embeddingDownNat ≅
      algebraicStalk φ x :=
  (embeddingDownNat.extendFunctor
    (ModuleCat (PresentationStalk.target φ x).right)).mapIso
    (Algebra.Extension.NaiveCotangent.reindexIso
      (Algebra.Generators.self (O₁.presheaf.stalk x)
        (PresentationStalk.target φ x).right)
      (PresentationStalk.generatorEquiv φ x))

/-- Lemma 17.31.4 (0D09): the canonical isomorphism from the ordinary stalk of the sheaf-level
naive cotangent complex to the algebraic naive cotangent complex of the induced morphism on
stalk rings. -/
@[stacks 0D09, stacks 08UO]
noncomputable def stalkIso (φ : O₁ ⟶ O₂) (x : X) :
    stalk φ x ≅ algebraicStalk φ x :=
  presentationStalkIso φ x ≪≫ polynomialStalkIso φ x ≪≫ reindexStalkIso φ x

/-- The forward map of `stalkIso` is the composite of the presentation, polynomial, and
generator-reindexing comparisons. -/
@[stacks 0D09 "naive cotangent stalk isomorphism hom",
  stacks 08UO "naive cotangent stalk isomorphism hom", simp]
theorem stalkIso_hom (φ : O₁ ⟶ O₂) (x : X) :
    (stalkIso φ x).hom =
      (presentationStalkIso φ x).hom ≫
        (polynomialStalkIso φ x).hom ≫
        (reindexStalkIso φ x).hom := sorry

/-- The inverse of `stalkIso` applies the generator reindexing, polynomial, and presentation
comparisons in reverse order. -/
@[stacks 0D09 "naive cotangent stalk isomorphism inverse",
  stacks 08UO "naive cotangent stalk isomorphism inverse", simp]
theorem stalkIso_inv (φ : O₁ ⟶ O₂) (x : X) :
    (stalkIso φ x).inv =
      (reindexStalkIso φ x).inv ≫
        (polynomialStalkIso φ x).inv ≫
        (presentationStalkIso φ x).inv := sorry

/-- The degree `-1` component of `stalkIso` is the composite of the presentation, polynomial,
and generator-reindexing comparisons. -/
@[stacks 0D09 "degree -1 naive cotangent stalk isomorphism hom",
  stacks 08UO "degree -1 naive cotangent stalk isomorphism hom"]
theorem stalkIso_hom_f_negOne (φ : O₁ ⟶ O₂) (x : X) :
    (stalkIso φ x).hom.f (-1) =
      (presentationStalkIso φ x).hom.f (-1) ≫
        (polynomialStalkIso φ x).hom.f (-1) ≫
        (reindexStalkIso φ x).hom.f (-1) := sorry

/-- The degree `0` component of `stalkIso` is the composite of the presentation, polynomial,
and generator-reindexing comparisons. -/
@[stacks 0D09 "degree 0 naive cotangent stalk isomorphism hom",
  stacks 08UO "degree 0 naive cotangent stalk isomorphism hom"]
theorem stalkIso_hom_f_zero (φ : O₁ ⟶ O₂) (x : X) :
    (stalkIso φ x).hom.f 0 =
      (presentationStalkIso φ x).hom.f 0 ≫
        (polynomialStalkIso φ x).hom.f 0 ≫
        (reindexStalkIso φ x).hom.f 0 := sorry

/-- The degree `-1` component of the inverse stalk isomorphism applies the three comparison
inverses in reverse order. -/
@[stacks 0D09 "degree -1 naive cotangent stalk isomorphism inverse",
  stacks 08UO "degree -1 naive cotangent stalk isomorphism inverse"]
theorem stalkIso_inv_f_negOne (φ : O₁ ⟶ O₂) (x : X) :
    (stalkIso φ x).inv.f (-1) =
      (reindexStalkIso φ x).inv.f (-1) ≫
        (polynomialStalkIso φ x).inv.f (-1) ≫
        (presentationStalkIso φ x).inv.f (-1) := sorry

/-- The degree `0` component of the inverse stalk isomorphism applies the three comparison
inverses in reverse order. -/
@[stacks 0D09 "degree 0 naive cotangent stalk isomorphism inverse",
  stacks 08UO "degree 0 naive cotangent stalk isomorphism inverse"]
theorem stalkIso_inv_f_zero (φ : O₁ ⟶ O₂) (x : X) :
    (stalkIso φ x).inv.f 0 =
      (reindexStalkIso φ x).inv.f 0 ≫
        (polynomialStalkIso φ x).inv.f 0 ≫
        (presentationStalkIso φ x).inv.f 0 := sorry

/-- The visible degree `-1 → 0` differential is compatible with the canonical stalk
isomorphism. -/
@[stacks 08UO "differential compatibility"]
theorem stalkIso_hom_d_negOne_zero (φ : O₁ ⟶ O₂) (x : X) :
    (stalkIso φ x).hom.f (-1) ≫ (algebraicStalk φ x).d (-1) 0 =
      (stalk φ x).d (-1) 0 ≫ (stalkIso φ x).hom.f 0 := sorry

omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
  [(Opens.grothendieckTopology X).HasSheafCompose
    (CategoryTheory.forget CommRingCat.{u})] in
/-- The visible differential of the stalkwise complex is the stalk of the canonical conormal
map. -/
theorem stalk_d_negOne_zero (φ : O₁ ⟶ O₂) (x : X) :
    (stalk φ x).d (-1) 0 =
      (SheafOfModules.stalkFunctorOfCommRing O₂ x).map
        (conormalMap (FreeAlgebra.Presentation.base O₁ (Under.mk φ))
          (FreeAlgebra.Presentation.map O₁ (Under.mk φ))) := sorry

namespace AlgebraicStalk

/-- Cohomological degree `-1` of the algebraic stalk is chain degree `1` of the naive cotangent
complex of the stalk-ring map. -/
noncomputable def negOneIso (φ : O₁ ⟶ O₂) (x : X) :
    (algebraicStalk φ x).X (-1) ≅
      (CommRingCat.Hom.naiveCotangent
        ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map φ.hom)).X 1 :=
  (CommRingCat.Hom.naiveCotangent
    ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map φ.hom)).extendXIso
      embeddingDownNat rfl

/-- Cohomological degree `0` of the algebraic stalk is chain degree `0` of the naive cotangent
complex of the stalk-ring map. -/
noncomputable def zeroIso (φ : O₁ ⟶ O₂) (x : X) :
    (algebraicStalk φ x).X 0 ≅
      (CommRingCat.Hom.naiveCotangent
        ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map φ.hom)).X 0 :=
  (CommRingCat.Hom.naiveCotangent
    ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map φ.hom)).extendXIso
      embeddingDownNat rfl

omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
  [HasWeakSheafify (Opens.grothendieckTopology X) CommRingCat.{u}]
  [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [(Opens.grothendieckTopology X).HasSheafCompose
    (CategoryTheory.forget CommRingCat.{u})]
  [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The visible differential of the algebraic stalk is the chain differential of the naive
cotangent complex, transported from homological degrees `1 → 0`. -/
theorem d_negOne_zero (φ : O₁ ⟶ O₂) (x : X) :
    (algebraicStalk φ x).d (-1) 0 =
      (negOneIso φ x).hom ≫
        (CommRingCat.Hom.naiveCotangent
          ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map φ.hom)).d 1 0 ≫
        (zeroIso φ x).inv := sorry

end AlgebraicStalk

end TopCat.Sheaf.NaiveCotangent
