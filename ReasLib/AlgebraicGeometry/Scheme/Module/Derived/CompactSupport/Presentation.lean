/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.DeligneSystem.Triangulated
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward

/-!
# Presentations of compactly supported derived pushforwards

This module defines positive inverse systems presenting compactly supported derived pushforwards
and their invariance under changing the system by an isomorphic bounded pro-object.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.Bounded.CohomologyIn
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport

variable {S : Scheme.{u}} [IsNoetherian S]
variable {X Y : Scheme.FiniteTypeSeparatedOver S}

/-- A positive inverse system presents the compactly supported pushforward of `K` along `f`
when, for some compactification of `f`, it presents the proper derived pushforward of a
Deligne-system tower whose value is `K`. -/
def IsPresentation (f : X ⟶ Y)
    (K : Dᵇ[SheafOfModules.isCoherent X.obj.left.ringCatSheaf])
    (A : PNatInverseSystem
      Dᵇ[SheafOfModules.isCoherent Y.obj.left.ringCatSheaf]) : Prop :=
  ∃ (P : Scheme.Compactification.Of Y.obj.left (Over.mk f.hom.left))
      (D : @DeligneSystem _ _ (Scheme.Compactification.Of.ι P) _
        (Scheme.FiniteTypeSeparatedOver.instIsNoetherian X) _),
    Nonempty (@DeligneSystem.value _ _ (Scheme.Compactification.Of.ι P) _
      (Scheme.FiniteTypeSeparatedOver.instIsNoetherian X) _ D ≅ K) ∧
      Nonempty (boundedProObject A ≅
        (@Pro.lim (DerivedCategory Y.obj.left.Modules) _
          (OrderDual ℕ+) _ _ _ _).obj
            (@DeligneSystem.tower _ _ (Scheme.Compactification.Of.ι P) _
              (Scheme.FiniteTypeSeparatedOver.instIsNoetherian X) _ D ⋙
              RingedSpace.moduleDerivedPushforward
              P.obj.right.hom.toShHom))

/-- A positive system is a compact-support presentation exactly when it arises from the
proper pushforward of a Deligne-system tower for some compactification. -/
theorem isPresentation_iff (f : X ⟶ Y)
    (K : Dᵇ[SheafOfModules.isCoherent X.obj.left.ringCatSheaf])
    (A : PNatInverseSystem
      Dᵇ[SheafOfModules.isCoherent Y.obj.left.ringCatSheaf]) :
    IsPresentation f K A ↔
      ∃ (P : Scheme.Compactification.Of Y.obj.left (Over.mk f.hom.left))
          (D : @DeligneSystem _ _ (Scheme.Compactification.Of.ι P) _
            (Scheme.FiniteTypeSeparatedOver.instIsNoetherian X) _),
        Nonempty (@DeligneSystem.value _ _ (Scheme.Compactification.Of.ι P) _
          (Scheme.FiniteTypeSeparatedOver.instIsNoetherian X) _ D ≅ K) ∧
          Nonempty (boundedProObject A ≅
            (@Pro.lim (DerivedCategory Y.obj.left.Modules) _
              (OrderDual ℕ+) _ _ _ _).obj
                (@DeligneSystem.tower _ _ (Scheme.Compactification.Of.ι P) _
                  (Scheme.FiniteTypeSeparatedOver.instIsNoetherian X) _ D ⋙
                  RingedSpace.moduleDerivedPushforward
                  P.obj.right.hom.toShHom)) :=
  Iff.rfl

namespace IsPresentation

/-- Compact-support presentations are invariant under replacing the positive system by one
with an isomorphic associated pro-object. -/
theorem ofProIso (f : X ⟶ Y)
    (K : Dᵇ[SheafOfModules.isCoherent X.obj.left.ringCatSheaf])
    {A B : PNatInverseSystem
      Dᵇ[SheafOfModules.isCoherent Y.obj.left.ringCatSheaf]}
    (hA : IsPresentation f K A)
    (e : boundedProObject A ≅ boundedProObject B) :
    IsPresentation f K B := sorry

end IsPresentation

end AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport
