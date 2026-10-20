module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Additive
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction
public import ReasLib.CategoryTheory.Adjunction.Derived.Unbounded

@[expose] public section

/-!
# Derived coextension of scalars

For a homomorphism of commutative rings, this file constructs the K-injective total
right-derived coextension-of-scalars functor and its adjunction with derived restriction of
scalars. Coextension retains the canonical target-ring action on `Hom`.
-/

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.ModuleCat

variable {A B : Type u} [CommRing A] [CommRing B]

/-- The K-injective total right-derived coextension-of-scalars functor. This is the
functorial `RHom_A(B, -)` valued in the derived category of `B`-modules. -/
noncomputable abbrev derivedCoextensionOfScalars (f : A →+* B) :
    DerivedCategory (ModuleCat.{u, u} A) ⥤ DerivedCategory (ModuleCat.{u, u} B) :=
  Adjunction.Derived.KInjective.right (ModuleCat.coextendScalars.{u, u, u} f)

/-- Derived restriction of scalars is left adjoint to K-injective total right-derived
coextension of scalars. -/
noncomputable def derivedRestrictionCoextensionAdjunction (f : A →+* B) :
    derivedRestrictionOfScalars f ⊣ derivedCoextensionOfScalars f :=
  Adjunction.Derived.KInjective.adjunction (DerivedRestriction.exact f)
    (ModuleCat.coextendScalars.{u, u, u} f)
    (ModuleCat.restrictCoextendScalarsAdj.{u, u, u} f)

/-- The Hom equivalence supplied by the derived restriction-coextension adjunction. -/
noncomputable def derivedRestrictionCoextensionHomEquiv (f : A →+* B)
    (K : DerivedCategory (ModuleCat.{u, u} B))
    (M : DerivedCategory (ModuleCat.{u, u} A)) :
    ((derivedRestrictionOfScalars f).obj K ⟶ M) ≃
      (K ⟶ (derivedCoextensionOfScalars f).obj M) :=
  (derivedRestrictionCoextensionAdjunction f).homEquiv K M

/-- Derived coextension of scalars is canonically a right adjoint. -/
noncomputable instance derivedCoextensionOfScalarsIsRightAdjoint (f : A →+* B) :
    (derivedCoextensionOfScalars f).IsRightAdjoint := sorry

/-- Applying the named derived restriction-coextension Hom equivalence agrees with the Hom
equivalence of its defining adjunction. -/
theorem derivedRestrictionCoextensionHomEquiv_apply (f : A →+* B)
    (K : DerivedCategory (ModuleCat.{u, u} B))
    (M : DerivedCategory (ModuleCat.{u, u} A))
    (g : (derivedRestrictionOfScalars f).obj K ⟶ M) :
    derivedRestrictionCoextensionHomEquiv f K M g =
      (derivedRestrictionCoextensionAdjunction f).homEquiv K M g := sorry

namespace DerivedCoextension

/-- The counit component from derived coextension followed by restriction of scalars. -/
noncomputable def counitApp (f : A →+* B)
    (K : DerivedCategory (ModuleCat.{u, u} A)) :
    (derivedRestrictionOfScalars f).obj ((derivedCoextensionOfScalars f).obj K) ⟶ K :=
  (derivedRestrictionCoextensionAdjunction f).counit.app K

end DerivedCoextension

end CategoryTheory.ModuleCat
