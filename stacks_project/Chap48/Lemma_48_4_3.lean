/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.BaseChange.Support
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

variable {X Y : Scheme.{u}}
variable [CompactSpace X] [QuasiSeparatedSpace X]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable (f : X ⟶ Y) (V : Y.Opens) (U : X.Opens)
variable (a : DerivedQCoh Y ⥤ DerivedQCoh X)
variable
  (aV : DerivedQCoh V.toScheme ⥤ DerivedQCoh U.toScheme)
  (jPush : DerivedQCoh V.toScheme ⥤ DerivedQCoh Y)
  (jPrimePush : DerivedQCoh U.toScheme ⥤ DerivedQCoh X)
  (jAdjunction : OpenImmersion.pullback V.ι ⊣ jPush)
  (jPrimeAdjunction : OpenImmersion.pullback U.ι ⊣ jPrimePush)
  (baseChangeIso :
    aV ⋙ jPrimePush ≅ jPush ⋙ a)

/- Lemma 48.4.3 -/
@[stacks 0A9N] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.supportOnComplement_iff_isIso_boundedBelow :
    ∀ {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      [CompactSpace Y] [QuasiSeparatedSpace Y]
      (f : X ⟶ Y) (V : Y.Opens) (U : X.Opens)
      (a : DerivedQCoh Y ⥤ DerivedQCoh X)
      (aV : DerivedQCoh V.toScheme ⥤ DerivedQCoh U.toScheme)
      (jPush : DerivedQCoh V.toScheme ⥤ DerivedQCoh Y)
      (jPrimePush : DerivedQCoh U.toScheme ⥤ DerivedQCoh X)
      (jAdjunction : OpenImmersion.pullback V.ι ⊣ jPush)
      (jPrimeAdjunction : OpenImmersion.pullback U.ι ⊣ jPrimePush)
      (baseChangeIso : aV ⋙ jPrimePush ≅ jPush ⋙ a)
      (aAdjunction : pushforwardCohomologyIn f ⊣ a)
      (hV : IsCompact (V : Set Y)) (hU : U = f ⁻¹ᵁ V),
      (∀ Q : DerivedQCoh Y,
        (t.plus : ObjectProperty (RingedSpace.ModuleDerived Y.toRingedSpace)) Q.obj →
        RingedSpace.ModuleDerived.IsSupportedOn Q.obj (V : Set Y)ᶜ →
        RingedSpace.ModuleDerived.IsSupportedOn (a.obj Q).obj (U : Set X)ᶜ) ↔
      ∀ K : DerivedQCoh Y,
        (t.plus : ObjectProperty (RingedSpace.ModuleDerived Y.toRingedSpace)) K.obj →
        IsIso ((DerivedBaseChange.mapOfRight
          jAdjunction jPrimeAdjunction baseChangeIso.inv).app K))

/- Lemma 48.4.3 (2) -/
@[stacks 0A9N] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.supportOnComplement_iff_isIso :
    ∀ {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      [CompactSpace Y] [QuasiSeparatedSpace Y]
      (f : X ⟶ Y) (V : Y.Opens) (U : X.Opens)
      (a : DerivedQCoh Y ⥤ DerivedQCoh X)
      (aV : DerivedQCoh V.toScheme ⥤ DerivedQCoh U.toScheme)
      (jPush : DerivedQCoh V.toScheme ⥤ DerivedQCoh Y)
      (jPrimePush : DerivedQCoh U.toScheme ⥤ DerivedQCoh X)
      (jAdjunction : OpenImmersion.pullback V.ι ⊣ jPush)
      (jPrimeAdjunction : OpenImmersion.pullback U.ι ⊣ jPrimePush)
      (baseChangeIso : aV ⋙ jPrimePush ≅ jPush ⋙ a)
      (aAdjunction : pushforwardCohomologyIn f ⊣ a)
      (hV : IsCompact (V : Set Y)) (hU : U = f ⁻¹ᵁ V),
      (∀ Q : DerivedQCoh Y,
        RingedSpace.ModuleDerived.IsSupportedOn Q.obj (V : Set Y)ᶜ →
        RingedSpace.ModuleDerived.IsSupportedOn (a.obj Q).obj (U : Set X)ᶜ) ↔
      ∀ K : DerivedQCoh Y,
        IsIso ((DerivedBaseChange.mapOfRight
          jAdjunction jPrimeAdjunction baseChangeIso.inv).app K))

/- Lemma 48.4.3 (3) -/
@[stacks 0A9N] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.supportOnComplement_of_preservesCoproducts :
    ∀ {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      [CompactSpace Y] [QuasiSeparatedSpace Y]
      (f : X ⟶ Y) (V : Y.Opens) (U : X.Opens)
      (a : DerivedQCoh Y ⥤ DerivedQCoh X)
      (aAdjunction : pushforwardCohomologyIn f ⊣ a)
      (hV : IsCompact (V : Set Y)) (hU : U = f ⁻¹ᵁ V)
      (h_coproducts : ∀ I : Type u, PreservesColimitsOfShape (Discrete I) a)
      (h_boundedBelow : ∀ Q : DerivedQCoh Y,
        (t.plus : ObjectProperty (RingedSpace.ModuleDerived Y.toRingedSpace)) Q.obj →
        RingedSpace.ModuleDerived.IsSupportedOn Q.obj (V : Set Y)ᶜ →
        RingedSpace.ModuleDerived.IsSupportedOn (a.obj Q).obj (U : Set X)ᶜ),
      ∀ Q : DerivedQCoh Y,
        RingedSpace.ModuleDerived.IsSupportedOn Q.obj (V : Set Y)ᶜ →
        RingedSpace.ModuleDerived.IsSupportedOn (a.obj Q).obj (U : Set X)ᶜ)

end AlgebraicGeometry.Scheme.DerivedQCoh
