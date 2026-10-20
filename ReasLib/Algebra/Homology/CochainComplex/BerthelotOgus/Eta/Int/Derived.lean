module

public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int.QuasiIso
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.CategoryTheory.Localization.Lifting.Computation

/-!
# The derived Berthelot-Ogus eta functor

Termwise `f`-torsion-free complexes form a localization model for the derived category when `f`
is a nonzerodivisor.  The eta model inverts the restricted quasi-isomorphisms, so the standard
localization lift constructs `Lη_f` together with one natural comparison isomorphism controlling
its action on both objects and morphisms.
@stack 0F7R
-/

@[expose] public section

open CategoryTheory ComplexShape
open scoped nonZeroDivisors

noncomputable section

universe u

namespace CochainComplex.BerthelotOgus.Int.Derived

variable {A : Type u} [CommRing A]
variable (f : nonZeroDivisors A)

/-- The inclusion of the canonical eta domain into all integer-indexed cochain complexes. -/
@[stacks 0F7R "canonical eta-domain inclusion"]
abbrev domainInclusion :
    Int.Domain.{u, u} (f : A) ⥤ CochainComplex (ModuleCat.{u} A) ℤ :=
  ObjectProperty.ι
    (HomologicalComplex.IsTermwiseSMulRegular (r := (f : A)) :
      ObjectProperty (CochainComplex (ModuleCat.{u} A) ℤ))

/-- Quasi-isomorphisms in the canonical eta domain. -/
@[stacks 0F7R "quasi-isomorphisms in the eta domain"]
abbrev quasiIso : MorphismProperty (Int.Domain.{u, u} (f : A)) :=
  (HomologicalComplex.quasiIso (ModuleCat.{u} A) (up ℤ)).inverseImage (domainInclusion f)

/-- The canonical realization of the eta domain in the derived category. -/
@[stacks 0F7R "derived realization of the eta domain"]
abbrev toDerived :
    Int.Domain.{u, u} (f : A) ⥤ DerivedCategory (ModuleCat.{u} A) :=
  domainInclusion f ⋙ DerivedCategory.Q

/-- The derived realization of a regular complex is its image under the standard localization
functor. -/
@[simp]
theorem toDerived_obj (K : Int.Domain.{u, u} (f : A)) :
    (toDerived f).obj K = DerivedCategory.Q.obj K.obj := sorry

/-- The derived realization of a morphism is the localization of its underlying cochain map. -/
@[simp]
theorem toDerived_map {K L : Int.Domain.{u, u} (f : A)} (φ : K ⟶ L) :
    (toDerived f).map φ = DerivedCategory.Q.map φ.hom := sorry

/-- Termwise `f`-torsion-free complexes form a localization model for the derived category. -/
@[stacks 0F7R "termwise-torsion-free localization", instance]
theorem toDerived_isLocalization : (toDerived f).IsLocalization (quasiIso f) := sorry

/-- The underived eta functor followed by localization to the derived category. -/
@[stacks 0F7R "localized underived eta model"]
abbrev model :
    Int.Domain.{u, u} (f : A) ⥤ DerivedCategory (ModuleCat.{u} A) :=
  Int.functor (f : A) ⋙ DerivedCategory.Q

/-- The eta model sends a regular complex to the derived image of its eta complex. -/
@[simp]
theorem model_obj (K : Int.Domain.{u, u} (f : A)) :
    (model f).obj K = DerivedCategory.Q.obj ((Int.functor (f : A)).obj K) := sorry

/-- The eta model sends a representative morphism to the localization of its eta map. -/
@[simp]
theorem model_map {K L : Int.Domain.{u, u} (f : A)} (φ : K ⟶ L) :
    (model f).map φ = DerivedCategory.Q.map ((Int.functor (f : A)).map φ) := sorry

/-- The localized eta model inverts quasi-isomorphisms in its canonical domain. -/
theorem model_inverts : (quasiIso f).IsInvertedBy (model f) := sorry

/-- Lemma 15.96.4, tag `0F7R`: the additive derived Berthelot-Ogus eta endofunctor. -/
@[stacks 0F7R "derived Berthelot-Ogus eta functor"]
noncomputable def functor :
    DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A) :=
  Localization.lift (model f) (model_inverts f) (toDerived f)

/-- The derived Berthelot-Ogus eta functor is additive. -/
@[stacks 0F7R "additivity", instance]
theorem additive : (functor f).Additive := sorry

/-- The natural comparison computing the derived eta functor on termwise torsion-free
representatives. -/
@[stacks 0F7R "derived eta comparison"]
noncomputable def comparison : toDerived f ⋙ functor f ≅ model f :=
  Localization.fac (model f) (model_inverts f) (toDerived f)

/-- The component of the derived eta comparison at a termwise torsion-free complex. -/
@[stacks 0F7R "derived eta comparison component"]
noncomputable def comparisonApp (K : Int.Domain.{u, u} (f : A)) :
    (functor f).obj ((toDerived f).obj K) ≅
      DerivedCategory.Q.obj ((Int.functor (f : A)).obj K) :=
  (comparison f).app K

/-- Naturality of the derived eta comparison is the computation rule on representative
morphisms. -/
@[reassoc]
theorem comparison_naturality {K L : Int.Domain.{u, u} (f : A)} (φ : K ⟶ L) :
    (functor f).map ((toDerived f).map φ) ≫ (comparison f).hom.app L =
      (comparison f).hom.app K ≫ (model f).map φ := sorry

/-- The derived eta functor maps a representative morphism by conjugating its eta image with the
canonical comparison isomorphisms. -/
theorem map_toDerived {K L : Int.Domain.{u, u} (f : A)} (φ : K ⟶ L) :
    (functor f).map ((toDerived f).map φ) =
      (comparison f).hom.app K ≫ (model f).map φ ≫ (comparison f).inv.app L := sorry

end CochainComplex.BerthelotOgus.Int.Derived
