/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Sites.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Algebra.FiniteTypeGeneration
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Algebra.Finite

/-!
# Integral quasi-coherent algebras on algebraic spaces

If `X` is a quasi-compact quasi-separated algebraic space over a scheme `S` and `A` is an
integral quasi-coherent `𝒪_X`-algebra, then `A` is the directed colimit of its finite
quasi-coherent subalgebras, and `A` is a directed colimit of finite and finitely presented
`𝒪_X`-algebras.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder

/-- A quasi-coherent `𝒪_X`-algebra is integral if, for every affine object of `X_étale`,
the algebra of sections is integral over the corresponding structure-sheaf sections. -/
class IsIntegral {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder) : Prop where
  /-- Section algebras on affine étale objects are integral. -/
  isIntegral_affineEtale :
    ∀ U : affineEtaleSite X,
      Algebra.IsIntegral Γ(U.obj.left.left, ⊤) (sectionRing A U.obj)

/-- Integrality of a quasi-coherent `𝒪_X`-algebra is equivalent to integrality of its
section algebras on every affine étale object. -/
theorem isIntegral_iff {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder) :
    IsIntegral A ↔
      ∀ U : affineEtaleSite X,
        Algebra.IsIntegral Γ(U.obj.left.left, ⊤) (sectionRing A U.obj) :=
  ⟨fun h ↦ h.isIntegral_affineEtale, fun h ↦ ⟨h⟩⟩

/-- Integrality of a quasi-coherent `𝒪_X`-algebra is equivalent to integrality of the
structure-map components on every affine étale object. -/
theorem isIntegral_iff_ringHom {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) :
    IsIntegral A ↔
      ∀ U : affineEtaleSite X, (structureMap A U.obj).hom.IsIntegral :=
  (isIntegral_iff A).trans (forall_congr' fun _ ↦ algebraMap_isIntegral_iff.symm)

/-- The structure sheaf `𝒪_X` is integral as an `𝒪_X`-algebra. -/
instance instIsIntegral_structureQcAlgebra {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsIntegral (structureQcAlgebra X) :=
  ⟨fun U ↦ by
    change Algebra.IsIntegral Γ(U.obj.left.left, ⊤) Γ(U.obj.left.left, ⊤)
    infer_instance⟩

/-- A finite quasi-coherent `𝒪_X`-algebra is integral. -/
instance instIsIntegral_of_isFinite {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) [IsFinite A] : IsIntegral A :=
  ⟨fun U ↦ by
    letI := IsFinite.moduleFinite_affineEtale (A := A) U
    infer_instance⟩

/-- The finite quasi-coherent subalgebras of a quasi-coherent `𝒪_X`-algebra. -/
def finiteQuasiCoherentSubalgebras {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) : Set (Subobject A.obj) :=
  {B | qcAlgebraUnderProperty X (B : Under (commStructureSheaf X)) ∧
      finiteProperty X (B : Under (commStructureSheaf X))}

/-- A subalgebra belongs to `finiteQuasiCoherentSubalgebras A` exactly when its carrier
algebra is quasi-coherent and finite. -/
@[simp] theorem mem_finiteQuasiCoherentSubalgebras {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) (B : Subobject A.obj) :
    B ∈ finiteQuasiCoherentSubalgebras A ↔
      qcAlgebraUnderProperty X (B : Under (commStructureSheaf X)) ∧
        finiteProperty X (B : Under (commStructureSheaf X)) :=
  Iff.rfl

/-- Finite quasi-coherent subalgebras are finite-type quasi-coherent subalgebras. -/
theorem finiteQuasiCoherentSubalgebras_subset_finiteTypeQuasiCoherentSubalgebras
    {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder) :
    finiteQuasiCoherentSubalgebras A ⊆ finiteTypeQuasiCoherentSubalgebras A :=
  by
    rintro B ⟨hB, hfin⟩
    obtain ⟨hB', hfin⟩ := hfin
    refine ⟨hB, ?_⟩
    intro U hU
    let C : X.QcAlgebraUnder := ⟨(B : Under (commStructureSheaf X)), hB'⟩
    letI := instAlgebra C U
    letI : Module.Finite Γ(U.left.left, ⊤) (sectionRing C U) :=
      hfin.moduleFinite_affineEtale ⟨U, hU⟩
    change (algebraMap Γ(U.left.left, ⊤) (sectionRing C U)).FiniteType
    exact RingHom.finiteType_algebraMap.mpr inferInstance

/-- For an integral quasi-coherent `𝒪_X`-algebra, finite-type quasi-coherent subalgebras
coincide with finite quasi-coherent subalgebras. -/
theorem finiteTypeQuasiCoherentSubalgebras_eq_finiteQuasiCoherentSubalgebras
    {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder) [IsIntegral A] :
    finiteTypeQuasiCoherentSubalgebras A = finiteQuasiCoherentSubalgebras A :=
  by
    apply Set.Subset.antisymm ?_
      (finiteQuasiCoherentSubalgebras_subset_finiteTypeQuasiCoherentSubalgebras A)
    rintro B ⟨hB, hft⟩
    refine ⟨hB, hB, ?_⟩
    let C : X.QcAlgebraUnder := ⟨(B : Under (commStructureSheaf X)), hB⟩
    constructor
    intro U
    letI := instAlgebra C U.obj
    letI := instAlgebra A U.obj
    letI : Algebra.FiniteType Γ(U.obj.left.left, ⊤) (sectionRing C U.obj) :=
      hft U.obj U.property
    letI : Algebra.IsIntegral Γ(U.obj.left.left, ⊤) (sectionRing A U.obj) :=
      IsIntegral.isIntegral_affineEtale (A := A) U
    haveI : Mono B.arrow.right := Under.mono_right_of_mono B.arrow
    haveI : Mono (InducedCategory.Hom.hom B.arrow.right) :=
      (sheafToPresheaf (smallEtaleTopology X) CommRingCat).map_mono B.arrow.right
    let φ : sectionRing C U.obj ⟶ sectionRing A U.obj :=
      (InducedCategory.Hom.hom B.arrow.right).app (Opposite.op U.obj)
    haveI : Mono φ := inferInstance
    let f : sectionRing C U.obj →ₐ[Γ(U.obj.left.left, ⊤)] sectionRing A U.obj :=
      { φ.hom with
        commutes' := fun r ↦ by
          have h := congrArg
            (fun k : commStructureSheaf X ⟶ A.obj.right ↦
              (InducedCategory.Hom.hom k).app (Opposite.op U.obj))
            (Under.w B.arrow)
          exact ConcreteCategory.congr_hom h r }
    letI : Algebra.IsIntegral Γ(U.obj.left.left, ⊤) (sectionRing C U.obj) :=
      Algebra.IsIntegral.of_injective f
        (ConcreteCategory.injective_of_mono_of_preservesPullback φ)
    exact Algebra.IsIntegral.finite

/-- The inclusion diagram of the finite quasi-coherent subalgebras of an algebra,
indexed by their inherited inclusion order. -/
def finiteSubalgebraDiagram {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) :
    finiteQuasiCoherentSubalgebras A ⥤ Under (commStructureSheaf X) :=
  (show Monotone (fun B : finiteQuasiCoherentSubalgebras A ↦ B.val) from
    fun _ _ h ↦ h).functor ⋙ Subobject.underlying

/-- The canonical inclusions of finite quasi-coherent subalgebras form a cocone
with point the ambient algebra. -/
def finiteSubalgebraCocone {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) : CategoryTheory.Limits.Cocone (finiteSubalgebraDiagram A) where
  pt := A.obj
  ι :=
    { app := fun B ↦ B.val.arrow
      naturality := fun B C f ↦ by
        change (finiteSubalgebraDiagram A).map f ≫ C.val.arrow =
          B.val.arrow ≫ 𝟙 A.obj
        rw [Category.comp_id]
        exact Subobject.underlying_arrow
            ((show Monotone (fun B : finiteQuasiCoherentSubalgebras A ↦ B.val) from
              fun _ _ h ↦ h).functor.map f) }

/-- Each leg of the canonical finite-subalgebra cocone is the corresponding
subobject inclusion. -/
@[simp] theorem finiteSubalgebraCocone_ι_app {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) (B : finiteQuasiCoherentSubalgebras A) :
    (finiteSubalgebraCocone A).ι.app B = B.val.arrow :=
  rfl

/-- On a quasi-compact quasi-separated algebraic space, the finite quasi-coherent
subalgebras of an integral quasi-coherent algebra form a nonempty directed family whose
inclusion cocone has the colimit universal property over the structure sheaf. -/
theorem finiteQuasiCoherentSubalgebras_directedColimit_of_isIntegral
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsQuasiCompact X]
    [IsAbsolutelyQuasiSeparated X] (A : X.QcAlgebraUnder) [IsIntegral A] :
    (finiteQuasiCoherentSubalgebras A).Nonempty ∧
      DirectedOn (· ≤ ·) (finiteQuasiCoherentSubalgebras A) ∧
        (∀ c : CategoryTheory.Limits.Cocone (finiteSubalgebraDiagram A),
          ∃! f : A.obj ⟶ c.pt, ∀ B : finiteQuasiCoherentSubalgebras A,
            B.val.arrow ≫ f = c.ι.app B) :=
  by
    let P (T : Set (Subobject A.obj)) : Prop :=
      T.Nonempty ∧ DirectedOn (· ≤ ·) T ∧
        (∀ c : CategoryTheory.Limits.Cocone
            ((show Monotone (fun B : T ↦ B.val) from fun _ _ h ↦ h).functor ⋙
              Subobject.underlying),
          ∃! f : A.obj ⟶ c.pt, ∀ B : T, B.val.arrow ≫ f = c.ι.app B)
    change P (finiteQuasiCoherentSubalgebras A)
    rw [← finiteTypeQuasiCoherentSubalgebras_eq_finiteQuasiCoherentSubalgebras A]
    exact finiteTypeQuasiCoherentSubalgebras_directedColimit A

/-- On a quasi-compact quasi-separated algebraic space, an integral quasi-coherent
`𝒪_X`-algebra is a filtered colimit of quasi-coherent algebras that are both finite and
finitely presented. -/
theorem finiteFinitelyPresentable_ind_of_isIntegral
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsQuasiCompact X]
    [IsAbsolutelyQuasiSeparated X] (A : X.QcAlgebraUnder) [IsIntegral A] :
    ObjectProperty.ind.{u}
      (fun B : Under (commStructureSheaf X) ↦
        finiteProperty X B ∧ finitelyPresentableProperty X B) A.obj :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder
