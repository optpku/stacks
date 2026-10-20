module

public import stacks_project.Chap91.Lemma_91_13_3_Difference

/-!
# Presentation witnesses for the Ext¹ deformation action

The representative includes its locally surjective polynomial presentation.
It is not a section onto the conormal of one arbitrarily fixed complex.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf
open SheafOfModules.RingedSite SheafOfModules.RingedSite.NaiveCotangent
open scoped DerivedExt

noncomputable section
universe c v w

namespace SheafOfModules.RingedSite.NaiveCotangent

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J CommRingCat.{w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [HasSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {A B : Sheaf J CommRingCat.{w}} (φ : A ⟶ B)
variable (G : SheafOfModules.{w} (ringSheaf J (Under.mk φ).right))
-- Local instance justification (defeq pin): all Ext and presentation maps use the standard derived quotient at the independent coefficient universe.
attribute [local instance] HasDerivedCategory.standard

/-- All presentation data and the exact derived equation representing an Ext¹ class. -/
structure ExtOnePresentation
    (ξ : Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (obj A (Under.mk φ)),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G))) where
  /-- The chosen generators on the site. -/
  generators : Sheaf J (Type w)
  /-- Evaluation of these generators in the target algebra. -/
  assignment : generators ⟶ FreeAlgebra.Presentation.generators (Under.mk φ)
  /-- The evaluation is an actual local presentation. -/
  locallySurjective : IsLocallySurjective (FreeAlgebra.evaluation (Under.mk φ) generators assignment).right
  /-- A morphism from the conormal of this presentation. -/
  conormalMap : (Presentation.ofGenerators generators assignment).X (-1) ⟶ G
  /-- The comparison to the source Ext¹ class; no unsupported inversion occurs. -/
  represents : Presentation.derivedComparison generators assignment ≫ ξ =
    conormalHomClass φ G generators assignment conormalMap

/-- Lemma 91.13.2 supplies exactly the data and equation of an Ext¹ presentation. -/
theorem exists_extOnePresentation
    (ξ : Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (obj A (Under.mk φ)),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G))) :
    Nonempty (ExtOnePresentation φ G ξ) := by
  obtain ⟨E, α, hα, δ, hδ⟩ := exists_conormalHomClass φ G ξ
  exact ⟨⟨E, α, hα, δ, hδ⟩⟩

/-- Choose a fully specified presentation witness, not a bare inverse or a fixed-conormal map. -/
def extOnePresentation
    (ξ : Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (obj A (Under.mk φ)),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G))) :
    ExtOnePresentation φ G ξ :=
  Classical.choice (exists_extOnePresentation φ G ξ)

/-- The selected witness retains the actual equation furnished by the canonical owner. -/
theorem extOnePresentation_represents
    (ξ : Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (obj A (Under.mk φ)),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G))) :
    Presentation.derivedComparison (extOnePresentation φ G ξ).generators
      (extOnePresentation φ G ξ).assignment ≫ ξ =
    conormalHomClass φ G (extOnePresentation φ G ξ).generators
      (extOnePresentation φ G ξ).assignment (extOnePresentation φ G ξ).conormalMap :=
  (extOnePresentation φ G ξ).represents

end SheafOfModules.RingedSite.NaiveCotangent

namespace SheafOfModules.RingedSite.FirstOrderThickening.Solution

-- Pin the same derived-category instance as the existing translation owner.
-- Local instance justification (defeq pin): all Ext and presentation maps use the standard derived quotient at the independent coefficient universe.
attribute [local instance] HasDerivedCategory.standard

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasWeakSheafify J CommRingCat.{w}] [J.WEqualsLocallyBijective CommRingCat.{w}]
variable [HasSheafify J AddCommGrpCat.{w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O_B' O_B O : Sheaf J CommRingCat.{w}}
variable {π : O_B' ⟶ O_B} [IsLocallySurjective π]
variable {hπ : KernelIdeal.IsSquareZero π} {fSharp : O_B ⟶ O}
variable {G : SheafOfModules.{w} (ringSheaf J O)}
variable {c : hπ.targetModule (KernelIdeal.quotientComparison_isIso π) ⟶
  (restrictionAlong fSharp).obj G}

/-- Translate using the actual locally-surjective presentation representing ξ. -/
def translatePresented
    (ξ : Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (obj O_B (Under.mk fSharp)),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G)))
    (P : ExtOnePresentation fSharp G ξ) (sol : Solution π hπ fSharp G c) :
    Solution π hπ fSharp G c :=
  -- Local instance justification (noncanonical choice): the selected Ext presentation carries the local-surjectivity witness needed for its graph pushout.
  letI := P.locallySurjective
  translateOf P.generators P.assignment P.conormalMap sol

/-- The translated middle algebra is the existing fiber-product-presentation pushout. -/
theorem translatePresented_middle
    (ξ : Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (obj O_B (Under.mk fSharp)),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G)))
    (P : ExtOnePresentation fSharp G ξ) (sol : Solution π hπ fSharp G c) :
    (translatePresented ξ P sol).middle =
      translateSheaf P.generators P.assignment P.conormalMap sol :=
  by
    -- Local instance justification (noncanonical choice): the selected Ext presentation carries the local-surjectivity witness needed for its graph pushout.
    letI := P.locallySurjective
    exact (translateOf_spec P.generators P.assignment P.conormalMap sol).1

/-- Difference uses the actual comparison cube of two extensions, not the
subtraction of lift-independent chosen conormal maps. -/
def differencePresented (S₁ S₂ : Solution π hπ fSharp G c) :
    Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (obj O_B (Under.mk fSharp)),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G)) :=
  Difference.extClass S₁ S₂

/-- The difference is exactly the canonical common-presentation obstruction. -/
theorem differencePresented_eq (S₁ S₂ : Solution π hπ fSharp G c) :
    differencePresented S₁ S₂ = Difference.extClass S₁ S₂ := rfl

end SheafOfModules.RingedSite.FirstOrderThickening.Solution
