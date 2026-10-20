module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.CompactSupportTrace
public import ReasLib.CategoryTheory.Abelian.StructureTransport
public import stacks_project.Chap59.Definition_59_77_1

/-! # Geometric Frobenius traces on stalks -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry MonoidalCategory Ring

universe u

noncomputable section

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k] [Fintype k]
variable {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
variable {Λ : Type u} [CommRing Λ]
variable [HasColimitsOfSize.{u, u} (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}}, HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}} (U : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [sheafAbelian : ∀ {Y : Scheme.{u}},
    Abelian (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ {Y : Scheme.{u}},
    HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- Derived geometric stalk of an étale module complex at a rational point. -/
abbrev geometricDerivedStalk {X : SchemeOverField k}
    (K : EtaleDerived X.left Λ) (x : 𝟙_ (SchemeOverField k) ⟶ X) :
    DerivedCategory (ModuleCat.{u} Λ) :=
  by
  cases funext (fun Y : Scheme.{u} ↦
    Abelian.structure_eq (sheafAbelian (Y := Y))
      (CategoryTheory.sheafIsAbelian (J := Y.smallEtaleTopology) (D := ModuleCat.{u} Λ)))
  exact CompactSupportTrace.geometricDerivedStalk K x

/-- Geometric Frobenius on the derived geometric stalk at a rational point. -/
abbrev geometricFrobeniusDerivedStalk {X : SchemeOverField k}
    (K : EtaleDerived X.left Λ) (x : 𝟙_ (SchemeOverField k) ⟶ X) :
    End (geometricDerivedStalk K x) :=
  by
  cases funext (fun Y : Scheme.{u} ↦
    Abelian.structure_eq (sheafAbelian (Y := Y))
      (CategoryTheory.sheafIsAbelian (J := Y.smallEtaleTopology) (D := ModuleCat.{u} Λ)))
  exact CompactSupportTrace.geometricFrobeniusDerivedStalk K x

/-- Sum of geometric Frobenius traces on the geometric stalks at rational points. -/
def traceGeometricFrobeniusStalks (X : SchemeOverField k)
    (K : EtaleDerived X.left Λ)
    (hK : ∀ x : (𝟙_ (SchemeOverField k) ⟶ X),
      DerivedCategory.IsPerfect (geometricDerivedStalk K x)) : Λ♮ :=
  by
  cases funext (fun Y : Scheme.{u} ↦
    Abelian.structure_eq (sheafAbelian (Y := Y))
      (CategoryTheory.sheafIsAbelian (J := Y.smallEtaleTopology) (D := ModuleCat.{u} Λ)))
  exact CompactSupportTrace.traceGeometricFrobeniusStalks K hK

end AlgebraicGeometry.SchemeOverField
