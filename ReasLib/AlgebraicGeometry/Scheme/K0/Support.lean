module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Support
public import ReasLib.AlgebraicGeometry.Scheme.K0

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The triangulated Grothendieck group of perfect derived `O_X`-modules supported on `T`. -/
abbrev K0WithSupport (X : Scheme.{u}) (T : Set X) : Type (u + 1) :=
  TriangulatedK0 (RingedSpace.ModuleDerived.PerfectSupportedOn T)

namespace K0WithSupport

/-- The supported-perfect object classes kill the triangle relations after support is
forgotten. -/
theorem relations_le_ker_forget (X : Scheme.{u}) (T : Set X) :
    TriangulatedK0.relations
        (RingedSpace.ModuleDerived.PerfectSupportedOn T) ≤
      (FreeAbelianGroup.lift fun K :
          RingedSpace.ModuleDerived.PerfectSupportedOn T ↦
        TriangulatedK0.of
          (⟨K.obj, K.property.1⟩ :
            RingedSpace.ModuleDerived.Perfect)).ker := sorry

/-- Forgetting the support condition induces an additive map to ordinary perfect `K₀`. -/
noncomputable def forget (X : Scheme.{u}) (T : Set X) :
    K0WithSupport X T →+ K0 X :=
  TriangulatedK0.lift
    (fun K ↦ TriangulatedK0.of
      (⟨K.obj, K.property.1⟩ :
        RingedSpace.ModuleDerived.Perfect))
    (relations_le_ker_forget X T)

/-- The forgetful map sends a supported-perfect generator to its ordinary perfect class. -/
theorem forget_of (X : Scheme.{u}) (T : Set X)
    (K : RingedSpace.ModuleDerived.PerfectSupportedOn T) :
    forget X T (TriangulatedK0.of K) =
      TriangulatedK0.of
        (⟨K.obj, K.property.1⟩ :
          RingedSpace.ModuleDerived.Perfect) := sorry

end K0WithSupport

end AlgebraicGeometry.Scheme
