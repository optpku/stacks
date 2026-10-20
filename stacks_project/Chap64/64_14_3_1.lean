module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Lefschetz.ProjectiveCurve
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry MonoidalCategory Ring

universe u

noncomputable section

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k] [Fintype k]
variable {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
variable {Λ : Type u} [Ring Λ] [Finite Λ]
variable [∀ {Y : Scheme.{u}}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}}, HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}} (U : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}},
    HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
    (smallEtalePullback f).op.HasLeftKanExtension P]
variable [∀ {A B C : Scheme.{u}} (f : B ⟶ A) (g : C ⟶ B),
    PreservesFiniteLimits
      (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ) ⋙
        Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ))]
variable [∀ {A B C : Scheme.{u}} (f : B ⟶ A) (g : C ⟶ B),
    PreservesFiniteColimits
      (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ) ⋙
        Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ))]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]

/- 64.14.3.1: Lefschetz trace formula. For a projective curve over a finite field
and a constructible Tor-finite complex over a finite, possibly noncommutative ring,
the global Lefschetz number equals the sum of local geometric Frobenius traces. -/
@[stacks 03U0] #check
  (AlgebraicGeometry.SchemeOverField.lefschetzTraceFormula :
    ∀ (X : SchemeOverField k) [Curve X] [Projective X.hom]
      (K : Scheme.Etale.Derived.FiniteRing.ConstructibleTorFinite (X := X.left) (Λ := Λ)),
      (isPerfect_geometricRGamma X K).traceNatural
        (geometricFrobeniusRGamma X K.obj) =
      CompactSupportTrace.traceGeometricFrobeniusStalks K.obj
        (fun x ↦ CompactSupportTrace.isPerfect_geometricDerivedStalk_of_finiteRing K x))

end AlgebraicGeometry.SchemeOverField
