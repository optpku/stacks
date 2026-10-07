module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Module.Quasicoherent.ActionTransport
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Module.Quasicoherent.Forget
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.CardinalGeneration.Small
public import ReasLib.CategoryTheory.ObjectProperty.Representatives

/-!
# Smallness of cardinal-generated equivariant quasi-coherent modules

Cardinal-generated equivariant quasi-coherent modules on a groupoid scheme form an
essentially small object property and consequently admit a set of representatives.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidScheme.QCoh

/-- Equivariant quasi-coherent modules whose underlying object is isomorphic to a fixed
quasi-coherent module form an essentially small object property. -/
theorem fiberEssentiallySmallOfUnderlyingObj {S : Scheme.{u}} (G : GroupoidScheme S)
    (Y : Scheme.QCoh G.U.left) :
    ObjectProperty.EssentiallySmall.{u + 1}
      (fun E : G.QCoh => Nonempty (E.obj ≅ Y)) := by
  let A := { a : (Scheme.QCoh.pullback G.t.left).obj Y ⟶
      (Scheme.QCoh.pullback G.s.left).obj Y // Cocycle G Y a ∧ Unit G Y a }
  let Q : ObjectProperty G.QCoh :=
    ObjectProperty.ofObj fun a : A => of Y a.1 a.2.1 a.2.2
  refine ⟨Q, inferInstance, ?_⟩
  rintro E ⟨e⟩
  let a : A := ⟨transportedAction E e.symm, transportedAction_spec E e.symm⟩
  refine ⟨rebaseAlongIso E e.symm, ⟨a⟩, ⟨?_⟩⟩
  exact (rebaseAlongIsoIso E e.symm).symm

/-- Cardinal generation of the underlying module sheaf is invariant under isomorphisms of
equivariant quasi-coherent modules. -/
theorem isKappaGenerated_isClosedUnderIsomorphisms {S : Scheme.{u}}
    (G : GroupoidScheme S) (κ : Cardinal.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms
      (fun E : G.QCoh => E.obj.obj.IsKappaGenerated κ) where
  of_iso e hE :=
    (SheafOfModules.isKappaGenerated_iff_of_iso
      ((Scheme.QCoh.inclusion G.U.left).mapIso ((forget G).mapIso e)) κ).mp hE

/-- Cardinal-generated equivariant quasi-coherent modules on a groupoid scheme form an
essentially small object property. -/
theorem isKappaGenerated_essentiallySmall {S : Scheme.{u}}
    (G : GroupoidScheme S) (κ : Cardinal.{u}) :
    ObjectProperty.EssentiallySmall.{u + 1}
      (fun E : G.QCoh => E.obj.obj.IsKappaGenerated κ) := by
  let P : ObjectProperty G.QCoh := fun E => E.obj.obj.IsKappaGenerated κ
  have h_map : ObjectProperty.EssentiallySmall.{u + 1} (P.map (forget G)) := by
    apply ObjectProperty.EssentiallySmall.of_le
      (Q := fun Y : Scheme.QCoh G.U.left => Y.obj.IsKappaGenerated κ)
    rintro Y ⟨E, hE, ⟨e⟩⟩
    exact (SheafOfModules.isKappaGenerated_iff_of_iso
      ((Scheme.QCoh.inclusion G.U.left).mapIso e) κ).mp hE
  have h_fiber : ∀ Y : Scheme.QCoh G.U.left,
      ObjectProperty.EssentiallySmall.{u + 1}
        (P ⊓ fun E => Nonempty ((forget G).obj E ≅ Y)) := by
    intro Y
    exact @ObjectProperty.EssentiallySmall.of_le _ _
      (P ⊓ fun E => Nonempty ((forget G).obj E ≅ Y))
      (fun E : G.QCoh => Nonempty (E.obj ≅ Y))
      (fiberEssentiallySmallOfUnderlyingObj G Y) (fun _ hE => hE.2)
  exact ObjectProperty.EssentiallySmall.of_functor P (forget G) h_map h_fiber

/-- There is a set of cardinal-generated equivariant quasi-coherent modules containing a
representative of every isomorphism class of cardinal-generated equivariant objects. -/
theorem exists_set_kappaGenerated_representatives {S : Scheme.{u}}
    (G : GroupoidScheme S) (κ : Cardinal.{u}) :
    ∃ T : Set G.QCoh,
      (∀ E ∈ T, E.obj.obj.IsKappaGenerated κ) ∧
        ∀ E : G.QCoh, E.obj.obj.IsKappaGenerated κ →
          ∃ E' ∈ T, Nonempty (E' ≅ E) := by
  obtain ⟨T, hT, h_representative⟩ :=
    @ObjectProperty.EssentiallySmall.exists_set_representatives _ _
      (fun E : G.QCoh => E.obj.obj.IsKappaGenerated κ)
      (isKappaGenerated_isClosedUnderIsomorphisms G κ)
      (isKappaGenerated_essentiallySmall G κ)
  refine ⟨T, hT, fun E hE => ?_⟩
  obtain ⟨E', ⟨hE', e⟩, _⟩ := h_representative E hE
  exact ⟨E', hE', e⟩

end AlgebraicGeometry.GroupoidScheme.QCoh
