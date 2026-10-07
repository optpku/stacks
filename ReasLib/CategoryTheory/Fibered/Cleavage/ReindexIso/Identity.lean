module

public import ReasLib.CategoryTheory.Fibered.Cleavage.ReindexIso.Composition
public import ReasLib.CategoryTheory.Fibered.StronglyCartesian.Comparison
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Identity comparisons for cleavage reindexing

This leaf owns the canonical identity comparison, its objectwise calculation rules, and the
section criterion for faithful reindexing.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

namespace Functor.Cleavage

variable {p : S ⥤ C} (χ : p.Cleavage)

/-- The ambient-domain comparison underlying the identity reindexing component.

It is the canonical `DomainIso.ofBaseIso` comparison between the chosen lift over `𝟙 U` and the
identity lift, with the base isomorphism specialized to `Iso.refl U`. -/
noncomputable abbrev Reindex.idAmbientIso
    (U : C) (x : Fiber p U) :
    x.1 ≅ ((𝟙 U)⁎[χ] x).1 :=
  IsStronglyCartesian.DomainIso.ofBaseIso (g := Iso.refl U) p
    (Category.id_comp (𝟙 U)).symm
    (χ.cartesianHom (𝟙 U) x) (𝟙 (x.1))
    (cartesianHom.isStronglyCartesian χ (𝟙 U) x)
    (Functor.IsHomLift.isStronglyCartesian_of_isIso
      (p := p) (f := 𝟙 U) (φ := 𝟙 (x.1)) (𝟙 x : x ⟶ x).2)

/-- The forward ambient identity comparison lies over `𝟙 U`. -/
theorem Reindex.idAmbientIso.hom.isHomLift
    (U : C) (x : Fiber p U) :
    p.IsHomLift (𝟙 U) (Reindex.idAmbientIso χ U x).hom := sorry

/-- The inverse ambient identity comparison lies over `𝟙 U`. -/
theorem Reindex.idAmbientIso.inv.isHomLift
    (U : C) (x : Fiber p U) :
    p.IsHomLift (𝟙 U) (Reindex.idAmbientIso χ U x).inv := sorry

/-- The component at `x` of the unit comparison `𝟭 ≅ (𝟙 U)⁎[χ]`. -/
noncomputable def Reindex.idIsoApp
    (U : C) (x : Fiber p U) :
    x ≅ (𝟙 U)⁎[χ] x :=
  { hom :=
      ⟨(Reindex.idAmbientIso χ U x).hom,
        Reindex.idAmbientIso.hom.isHomLift χ U x⟩
    inv :=
      ⟨(Reindex.idAmbientIso χ U x).inv,
        Reindex.idAmbientIso.inv.isHomLift χ U x⟩
    hom_inv_id := Fiber.hom_ext (Reindex.idAmbientIso χ U x).hom_inv_id
    inv_hom_id := Fiber.hom_ext (Reindex.idAmbientIso χ U x).inv_hom_id }

/-- The forward unit-comparison component factors the chosen identity pullback arrow through
the identity of `x`. -/
@[reassoc]
theorem Reindex.idIsoApp.hom.fac
    (U : C) (x : Fiber p U) :
    (Reindex.idIsoApp χ U x).hom.1 ≫ χ.cartesianHom (𝟙 U) x =
      𝟙 (x.1) := sorry
/- Proof strategy: unfold `Reindex.idIsoApp` and apply `IsCartesian.fac` to the
domain-uniqueness isomorphism between the identity and chosen cartesian arrows. -/

/-- The inverse unit-comparison component is the chosen pullback arrow along the identity. -/
@[simp, reassoc]
theorem Reindex.idIsoApp.inv.eq_cartesianHom
    (U : C) (x : Fiber p U) :
    (Reindex.idIsoApp χ U x).inv.1 = χ.cartesianHom (𝟙 U) x := sorry
/- Proof strategy: insert `Reindex.idIsoApp.hom.fac` and cancel the inverse-hom pair of
`Reindex.idIsoApp`. -/

/-- Naturality of the componentwise unit comparison. -/
theorem Reindex.idIsoApp.hom.naturality
    (U : C) {x y : Fiber p U} (φ : x ⟶ y) :
    φ ≫ (Reindex.idIsoApp χ U y).hom =
      (Reindex.idIsoApp χ U x).hom ≫ ((𝟙 U)⁎[χ]).map φ := sorry
/- Proof strategy: forget to `S`, postcompose with the chosen cartesian arrow over `𝟙 U`,
and use `reindexMap.fac` plus `Reindex.idIsoApp.hom.fac`; cartesian uniqueness finishes. -/

/-- Inverse naturality of the componentwise unit comparison. -/
theorem Reindex.idIsoApp.inv.naturality
    (U : C) {x y : Fiber p U} (φ : x ⟶ y) :
    ((𝟙 U)⁎[χ]).map φ ≫ (Reindex.idIsoApp χ U y).inv =
      (Reindex.idIsoApp χ U x).inv ≫ φ := sorry

/-- Conjugating a fiber morphism by the unit comparison gives its reindexing along the
identity. -/
@[reassoc]
theorem Reindex.idIsoApp.conjugation.toReindex
    (U : C) {x y : Fiber p U} (φ : x ⟶ y) :
    (Reindex.idIsoApp χ U x).inv ≫ φ ≫
        (Reindex.idIsoApp χ U y).hom =
      ((𝟙 U)⁎[χ]).map φ := sorry

/-- Conjugating identity reindexing by the unit comparison recovers the original fiber
morphism. -/
@[reassoc]
theorem Reindex.idIsoApp.conjugation.toIdentity
    (U : C) {x y : Fiber p U} (φ : x ⟶ y) :
    (Reindex.idIsoApp χ U x).hom ≫ ((𝟙 U)⁎[χ]).map φ ≫
        (Reindex.idIsoApp χ U y).inv =
      φ := sorry

/-- Definition 4.33.6 (2), Lemma 4.33.7 (2) (Stacks 02XN/02XO): the canonical unit comparison
`α_U : 𝟭 (Fiber p U) ≅ (𝟙 U)⁎[χ]`. -/
@[stacks 02XN, stacks 02XO "(2)"]
noncomputable def Reindex.idIso
    (U : C) :
    𝟭 (Fiber p U) ≅ (𝟙 U)⁎[χ] :=
  NatIso.ofComponents (Reindex.idIsoApp χ U)
    (fun φ ↦ Reindex.idIsoApp.hom.naturality χ U φ)

/-- The forward component of the bundled unit comparison is its named objectwise
comparison. -/
@[simp]
theorem Reindex.idIso.hom.app
    (U : C) (x : Fiber p U) :
    (Reindex.idIso χ U).hom.app x = (Reindex.idIsoApp χ U x).hom := sorry

/-- The inverse component of the bundled unit comparison is its named objectwise
comparison. -/
@[simp]
theorem Reindex.idIso.inv.app
    (U : C) (x : Fiber p U) :
    (Reindex.idIso χ U).inv.app x = (Reindex.idIsoApp χ U x).inv := sorry

/-- The unit comparison is uniquely characterized by its identity-pullback factorization. -/
theorem Reindex.idIso.unique
    (U : C) (α : 𝟭 (Fiber p U) ≅ (𝟙 U)⁎[χ])
    (hα : ∀ x : Fiber p U,
      (α.hom.app x).1 ≫ χ.cartesianHom (𝟙 U) x = 𝟙 (x.1)) :
    α = Reindex.idIso χ U := sorry
/- Proof strategy: ext objectwise and apply cartesian uniqueness after forgetting to `S`;
`hα` and `Reindex.idIsoApp.hom.fac` give the same postcomposition. -/

/-- Reindexing along a base morphism with a section is faithful. The comparison for
`s ≫ f = 𝟙 U` exhibits reindexing along `s` as a left inverse up to natural isomorphism. -/
theorem Reindex.faithfulOfSection
    {U V : C} (f : V ⟶ U) (s : U ⟶ V) (hs : s ≫ f = 𝟙 U) :
    Functor.Faithful (χ.reindex f) := sorry

end Functor.Cleavage

end CategoryTheory
