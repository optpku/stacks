/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.StructureSheaf
import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.Acyclic
import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.Pushforward

/-!
# Derived pushforward along an affine morphism

Derived direct image along the canonical morphism to the pushed-forward structure sheaf is an
equivalence on derived modules with quasicoherent cohomology. Its composite with restriction of
scalars agrees with ordinary derived pushforward.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

variable {X S : Scheme.{u}}

namespace affinePushforwardToPushforwardStructure

/-- For an affine morphism, derived direct image to `(S, f_*𝒪_X)` preserves quasicoherent
cohomology. -/
theorem mapsTo (f : X ⟶ S) [IsAffineHom f] :
    DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ≤
      (DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty
          (RingedSpace.Hom.PushforwardStructure.target f.toShHom))).inverseImage
        (RingedSpace.moduleDerivedPushforward
          (RingedSpace.Hom.PushforwardStructure.lift f.toShHom)) := sorry

end affinePushforwardToPushforwardStructure

/-- Derived direct image along `X ⟶ (S, f_*𝒪_X)`, restricted to derived modules with
quasicoherent cohomology. -/
noncomputable def affinePushforwardToPushforwardStructure (f : X ⟶ S) [IsAffineHom f] :
    DerivedCategory.CohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ⥤
      PushforwardQCoh f :=
  FullSubcategory.restrict
    (RingedSpace.moduleDerivedPushforward
      (RingedSpace.Hom.PushforwardStructure.lift f.toShHom))
    (affinePushforwardToPushforwardStructure.mapsTo f)

namespace affinePushforwardToPushforwardStructure

/-- Derived direct image to `(S, f_*𝒪_X)` is an equivalence for an affine morphism. -/
instance isEquivalence (f : X ⟶ S) [IsAffineHom f] :
    Functor.IsEquivalence (affinePushforwardToPushforwardStructure f) := sorry

/-- Restriction of scalars after affine derived pushforward is naturally isomorphic to the
usual derived pushforward restricted to quasicoherent cohomology. -/
theorem compRestriction_isomorphic (f : X ⟶ S) [IsAffineHom f] :
    IsIsomorphic
      (affinePushforwardToPushforwardStructure f ⋙ pushforwardQCohRestriction f)
      (pushforwardCohomologyIn f) := sorry

end affinePushforwardToPushforwardStructure

namespace pushforwardCohomologyIn

/-- Derived pushforward on complexes with quasicoherent cohomology reflects isomorphisms along
an affine morphism. -/
instance reflectsIsomorphisms_of_isAffineHom (f : X ⟶ S) [IsAffineHom f] :
    (pushforwardCohomologyIn f).ReflectsIsomorphisms := sorry

end pushforwardCohomologyIn

/-- For a morphism of commutative rings `φ : A ⟶ B`, derived pushforward along
`Spec.map φ : Spec B ⟶ Spec A` intertwines the inverse affine global-sections
equivalences with derived restriction of scalars along `φ.hom`. -/
theorem affinePushforwardSquare_isomorphic {A B : CommRingCat.{u}} (φ : A ⟶ B) :
    IsIsomorphic
      ((affineGlobalSections B).inv ⋙ pushforwardCohomologyIn (Spec.map φ))
      (ModuleCat.derivedRestrictionOfScalars φ.hom ⋙
        (affineGlobalSections A).inv) := sorry

/-- Along an affine morphism, derived quasicoherent pushforward commutes up to natural
isomorphism with comparison to derived modules having quasicoherent cohomology. -/
theorem pushforwardComparison_isomorphic_of_isAffineHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffineHom f] :
    IsIsomorphic (QCoh.Derived.pushforward f ⋙ comparison Y)
      (comparison X ⋙ pushforwardCohomologyIn f) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
