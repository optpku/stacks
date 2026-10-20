module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic.Characterization
public import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Basic
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Right-Derived Functors of Exact Functors

@stack 015F

An exact functor already inverts quasi-isomorphisms after passage to the target derived category.
This leaf exposes the resulting definedness, computation, acyclicity, and vanishing APIs without
choosing resolutions.
-/

open CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

universe w vA vB uA uB

namespace CategoryTheory.Functor.RightDerived.Exact

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} B]
  (F : A ⥤ B) [F.Additive]

/-- The functor on the homotopy category induced by an exact functor inverts
quasi-isomorphisms. -/
@[stacks 015F "exact functors invert quasi-isomorphisms"]
theorem isInvertedBy
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (HomotopyCategory.quasiIso A (up ℤ)).IsInvertedBy (Functor.Homotopy.toDerived F) := by
  rw [HomotopyCategory.quasiIso_eq_quasiIso_map_quotient,
    MorphismProperty.IsInvertedBy.map_iff]
  apply (MorphismProperty.IsInvertedBy.iff_of_iso _ (Functor.Homotopy.cochainIso F)).2
  intro K L f hf
  have : QuasiIso f := hf
  have : QuasiIso ((F.mapHomologicalComplex (up ℤ)).map f) := inferInstance
  change IsIso (DerivedCategory.Q.map ((F.mapHomologicalComplex (up ℤ)).map f))
  infer_instance

/-- The canonical functor induced on derived categories is a right-derived functor. -/
@[stacks 015F]
noncomputable instance isRightDerived
    [HasDerivedCategory.{w} A]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    F.mapDerivedCategory.IsRightDerivedFunctor F.mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso A (up ℤ)) := by
  let ff := Localization.fullyFaithfulWhiskeringLeft
    (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A)
    (HomotopyCategory.quasiIso A (up ℤ)) (DerivedCategory B)
  refine ⟨⟨⟨IsInitial.ofUniqueHom
    (fun E ↦ StructuredArrow.homMk
      (ff.preimage (F.mapDerivedCategoryFactorsh.hom ≫ E.hom)) ?_)
    (fun E φ ↦ ?_)⟩⟩⟩
  · change F.mapDerivedCategoryFactorsh.inv ≫
      ((whiskeringLeft _ _ _).obj DerivedCategory.Qh).map
        (ff.preimage (F.mapDerivedCategoryFactorsh.hom ≫ E.hom)) = E.hom
    rw [ff.map_preimage]
    simp
  · apply StructuredArrow.hom_ext
    apply ff.map_injective
    change whiskerLeft DerivedCategory.Qh φ.right =
      ((whiskeringLeft _ _ _).obj DerivedCategory.Qh).map
        (ff.preimage (F.mapDerivedCategoryFactorsh.hom ≫ E.hom))
    rw [ff.map_preimage]
    apply (cancel_epi F.mapDerivedCategoryFactorsh.inv).1
    simpa only [Iso.inv_hom_id_assoc, whiskeringLeft, LeftExtension.mk, StructuredArrow.mk] using StructuredArrow.w φ

/-- The unbounded right-derived functor of an exact functor is source-defined everywhere. -/
@[stacks 015F]
noncomputable instance everywhereDefined
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    CategoryTheory.Functor.RightDerived.EverywhereDefined (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) := sorry

/-- The unbounded right-derived functor of an exact functor exists as a total functor. -/
@[stacks 015F]
noncomputable instance hasFunctor
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (Functor.Homotopy.toDerived F).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ)) := by
  let W := HomotopyCategory.quasiIso A (up ℤ)
  let RF := Localization.lift (Functor.Homotopy.toDerived F) (isInvertedBy F) W.Q
  let e := Localization.fac (Functor.Homotopy.toDerived F) (isInvertedBy F) W.Q
  let ff := Localization.fullyFaithfulWhiskeringLeft W.Q W (DerivedCategory B)
  have universal : (LeftExtension.mk RF e.inv).IsUniversal :=
    IsInitial.ofUniqueHom
      (fun E ↦ StructuredArrow.homMk (ff.preimage (e.hom ≫ E.hom)) (by
        change e.inv ≫ ((whiskeringLeft _ _ _).obj W.Q).map
          (ff.preimage (e.hom ≫ E.hom)) = E.hom
        rw [ff.map_preimage]
        simp))
      (fun E φ ↦ by
        apply StructuredArrow.hom_ext
        apply ff.map_injective
        change whiskerLeft W.Q φ.right =
          ((whiskeringLeft _ _ _).obj W.Q).map (ff.preimage (e.hom ≫ E.hom))
        rw [ff.map_preimage]
        apply (cancel_epi e.inv).1
        simpa only [Iso.inv_hom_id_assoc, whiskeringLeft, LeftExtension.mk, StructuredArrow.mk] using StructuredArrow.w φ)
  have : RF.IsRightDerivedFunctor e.inv W := ⟨⟨⟨universal⟩⟩⟩
  exact HasRightDerivedFunctor.mk' (RF := RF) (α := e.inv)

/-- Every homotopy object computes the unbounded right-derived functor of an exact functor. -/
@[stacks 015F]
theorem computesAt
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : HomotopyCategory A (up ℤ)) :
    CategoryTheory.Functor.RightDerived.ComputesAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K := sorry

/-- Every object is right acyclic for an exact functor. -/
@[stacks 015F]
theorem isAcyclic
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (X : A) : CategoryTheory.Functor.RightAcyclic F X := sorry

namespace Bounded

/-- The bounded-below functor induced by an exact functor inverts quasi-isomorphisms. -/
@[stacks 015F "bounded exact functors invert quasi-isomorphisms"]
theorem isInvertedBy
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (HomotopyCategory.Plus.quasiIso A).IsInvertedBy F.toBoundedBelowDerived := sorry

/-- The bounded-below right-derived functor of an exact functor is source-defined everywhere. -/
@[stacks 015F]
noncomputable instance everywhereDefined
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    CategoryTheory.Functor.RightDerived.EverywhereDefined F.toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso A) := sorry

/-- The bounded-below right-derived functor of an exact functor exists as a total functor. -/
@[stacks 015F]
noncomputable instance hasFunctor
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A) := sorry

/-- Every bounded-below homotopy object computes the right-derived functor of an exact functor. -/
@[stacks 015F]
theorem computesAt
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : HomotopyCategory.Plus A) :
    CategoryTheory.Functor.RightDerived.ComputesAt F.toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso A) K := sorry

/-- Every object is bounded-below right acyclic for an exact functor. -/
@[stacks 015F]
theorem isAcyclic
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (X : A) : CategoryTheory.Functor.RightAcyclic.Bounded F X := sorry

/-- Every positive degree of a bounded-below right-derived functor of an exact functor vanishes. -/
@[stacks 015F]
theorem vanishesAboveZero
    [HasDerivedCategory.{w} A]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [(𝟭 A).toBoundedBelowDerived.IsLocalization
      (HomotopyCategory.Plus.quasiIso A)]
    (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (η : F.toBoundedBelowDerived ⟶ (𝟭 A).toBoundedBelowDerived ⋙ RF)
    [RF.IsRightDerivedFunctor η (HomotopyCategory.Plus.quasiIso A)]
    (X : A) : CategoryTheory.Functor.RightDerived.Bounded.Vanishes.aboveZero RF X := sorry

end Bounded

/-- Every positive ordinary right-derived degree of an exact functor vanishes. -/
@[stacks 015F]
theorem vanishesAboveZero
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [HasInjectiveResolutions A] (X : A) :
    CategoryTheory.Functor.RightDerived.Vanishes.aboveZero F X := sorry

end CategoryTheory.Functor.RightDerived.Exact
