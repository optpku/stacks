module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Flat
public import ReasLib.Topology.ConnectedComponents.Set

/-!
# Canonical scheme structures on connected components

Each connected component of a scheme has unique ideal-sheaf data whose associated closed
immersion is flat and whose support is the given component. The canonical datum
`Scheme.connectedComponentIdeal` is the germ-vanishing ideal sheaf of the component.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- A connected component of a scheme, as a closed subset. -/
def connectedComponentCloseds (X : Scheme.{u}) (C : ConnectedComponents X) :
    TopologicalSpace.Closeds X :=
  ⟨C.set, by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe C
    rw [ConnectedComponents.set_coe]
    exact isClosed_connectedComponent⟩

/-- A connected component of a scheme is stable under generalization. -/
theorem stableUnderGeneralization_connectedComponentCloseds
    (X : Scheme.{u}) (C : ConnectedComponents X) :
    StableUnderGeneralization ((X.connectedComponentCloseds C : TopologicalSpace.Closeds X) :
      Set X) := sorry

/-- The canonical scheme structure on a connected component: the ideal sheaf of sections whose
germs vanish along the component. -/
noncomputable def connectedComponentIdeal (X : Scheme.{u}) (C : ConnectedComponents X) : X.IdealSheafData :=
  IdealSheafData.germVanishing C.set

/-- The canonical closed immersion of a connected component is flat. -/
theorem flat_connectedComponentIdeal (X : Scheme.{u}) (C : ConnectedComponents X) :
    Flat (X.connectedComponentIdeal C).subschemeι :=
  IdealSheafData.flat_subschemeι_germVanishing (X.connectedComponentCloseds C)
    (X.stableUnderGeneralization_connectedComponentCloseds C)

/-- The canonical scheme structure on a connected component has support that component. -/
theorem support_connectedComponentIdeal (X : Scheme.{u}) (C : ConnectedComponents X) :
    ((X.connectedComponentIdeal C).support : Set X) = C.set :=
  IdealSheafData.support_germVanishing (X.connectedComponentCloseds C)
    (X.stableUnderGeneralization_connectedComponentCloseds C)

/-- A flat ideal-sheaf datum supported on a connected component is the canonical one. -/
theorem eq_connectedComponentIdeal (X : Scheme.{u}) (C : ConnectedComponents X)
    (I : X.IdealSheafData) (hI : Flat I.subschemeι) (h_support : (I.support : Set X) = C.set) :
    I = X.connectedComponentIdeal C :=
  IdealSheafData.eq_of_flat_of_support_eq I _ hI (X.flat_connectedComponentIdeal C)
    (h_support.trans (X.support_connectedComponentIdeal C).symm)

/-- A connected component of a scheme supports a unique ideal-sheaf datum whose associated
closed immersion is flat. -/
theorem existsUnique_flatIdealSheafData_connectedComponent
    (X : Scheme.{u}) (C : ConnectedComponents X) :
    ∃! I : X.IdealSheafData,
      Flat I.subschemeι ∧ (I.support : Set X) = C.set :=
  ⟨X.connectedComponentIdeal C,
    ⟨X.flat_connectedComponentIdeal C, X.support_connectedComponentIdeal C⟩,
    fun I hI ↦ X.eq_connectedComponentIdeal C I hI.1 hI.2⟩

end AlgebraicGeometry.Scheme
