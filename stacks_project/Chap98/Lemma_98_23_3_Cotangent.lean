module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Single
public import Mathlib.RingTheory.Kaehler.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Ext.Functor
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Canonical
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Derived

/-!
# Derived maps of naive cotangent objects

The self-presentation augmentation `NL{A⁄Λ} ⟶ Ω[A⁄Λ][0]`, the homology of
derived scalar extension of a map into `NL{A⁄Λ}`, and the degree-zero Ext
class of a derived morphism into a single module.
-/

@[expose] public section

open CategoryTheory Algebra
open Algebra.Generators
open DerivedCategory
open HomologicalComplex
open ComplexShape
open scoped NaiveCotangent

noncomputable section

universe u

namespace Algebra.NaiveCotangent

variable {Λ A : Type u} [CommRing Λ] [CommRing A] [Algebra Λ A]

/-- The self-presentation augmentation `d ≫ toKaehler` vanishes. -/
theorem toKaehler_comp_d :
    (Algebra.naiveCotangent Λ A).d 1 0 ≫
      ModuleCat.ofHom (Generators.self Λ A).toExtension.toKaehler = 0 :=
  sorry

/-- The augmentation `NL{A⁄Λ} ⟶ Ω[A⁄Λ][0]` in the derived category, induced by
the `toKaehler` map of the self-presentation. -/
def naiveCotangentToKaehler :
    Algebra.naiveCotangentObject Λ A ⟶
      (singleFunctor (ModuleCat A) 0).obj (ModuleCat.of A Ω[A⁄Λ]) :=
  DerivedCategory.Q.map
    (extendMap
        ((ChainComplex.toSingle₀Equiv (Algebra.naiveCotangent Λ A)
            (ModuleCat.of A Ω[A⁄Λ])).symm
          ⟨ModuleCat.ofHom (Generators.self Λ A).toExtension.toKaehler,
            toKaehler_comp_d⟩)
        embeddingDownNat ≫
      (extendSingleIso embeddingDownNat (ModuleCat.of A Ω[A⁄Λ])
        (0 : ℕ) (0 : ℤ) rfl).hom)

/-- `naiveCotangentToKaehler` is the derived image of the extended `toKaehler`
augmentation. -/
theorem naiveCotangentToKaehler_eq :
    naiveCotangentToKaehler =
      DerivedCategory.Q.map
        (extendMap
            ((ChainComplex.toSingle₀Equiv (Algebra.naiveCotangent Λ A)
                (ModuleCat.of A Ω[A⁄Λ])).symm
              ⟨ModuleCat.ofHom (Generators.self Λ A).toExtension.toKaehler,
                toKaehler_comp_d⟩)
            embeddingDownNat ≫
          (extendSingleIso embeddingDownNat (ModuleCat.of A Ω[A⁄Λ])
            (0 : ℕ) (0 : ℤ) rfl).hom) :=
  sorry

variable {k : Type u} [Field k] [Algebra A k]

/-- The degree-`i` homology map of derived scalar extension of `ξ` along
`A → k`. -/
def homologyMap {E : Minus (ModuleCat.{u} A)}
    (ξ : Minus.ι.obj E ⟶ naiveCotangentObject Λ A) (i : ℤ) :
    (homologyFunctor (ModuleCat k) i).obj
      ((ModuleCat.derivedExtensionOfScalars (algebraMap A k)).obj
        (Minus.ι.obj E)) ⟶
    (homologyFunctor (ModuleCat k) i).obj
      ((ModuleCat.derivedExtensionOfScalars (algebraMap A k)).obj
        (naiveCotangentObject Λ A)) :=
  (homologyFunctor (ModuleCat k) i).map
    ((ModuleCat.derivedExtensionOfScalars (algebraMap A k)).map ξ)

/-- `homologyMap ξ i` is the homology functor applied to derived extension of
scalars of `ξ`. -/
theorem homologyMap_eq {E : Minus (ModuleCat.{u} A)}
    (ξ : Minus.ι.obj E ⟶ naiveCotangentObject Λ A) (i : ℤ) :
    homologyMap ξ i =
      (homologyFunctor (ModuleCat k) i).map
        ((ModuleCat.derivedExtensionOfScalars (algebraMap A k)).map ξ) :=
  sorry

/-- The Ext class in `Ext^0_A(K, M)` of a derived morphism `K ⟶ M[0]`. -/
def extObjOfHom {K : DerivedCategory (ModuleCat A)} {M : ModuleCat A}
    (f : K ⟶ (singleFunctor (ModuleCat A) 0).obj M) :
    (DerivedCategory.Ext.moduleFunctor K (0 : ℤ)).obj M :=
  f ≫ (shiftFunctorZero (DerivedCategory (ModuleCat A)) ℤ).inv.app _

/-- `extObjOfHom` sends a derived morphism `K ⟶ M[0]` to the corresponding
degree-zero Ext class. -/
theorem extObjOfHom_eq {K : DerivedCategory (ModuleCat A)} {M : ModuleCat A}
    (f : K ⟶ (singleFunctor (ModuleCat A) 0).obj M) :
    extObjOfHom f =
      f ≫ (shiftFunctorZero (DerivedCategory (ModuleCat A)) ℤ).inv.app _ :=
  sorry

end Algebra.NaiveCotangent
