module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CompactSupport.Presentation

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.Bounded.CohomologyIn
open scoped DerivedCategory.CohomologyIn

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport

variable {S : Scheme.{u}} [IsNoetherian S]
variable {X Y : Scheme.FiniteTypeSeparatedOver S}

#check (IsPresentation :
  (X ⟶ Y) →
    Dᵇ[SheafOfModules.isCoherent X.obj.left.ringCatSheaf] →
    PNatInverseSystem Dᵇ[SheafOfModules.isCoherent Y.obj.left.ringCatSheaf] → Prop)

#check (isPresentation_iff :
  ∀ (f : X ⟶ Y)
    (K : Dᵇ[SheafOfModules.isCoherent X.obj.left.ringCatSheaf])
    (A : PNatInverseSystem
      Dᵇ[SheafOfModules.isCoherent Y.obj.left.ringCatSheaf]),
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
                  P.obj.right.hom.toShHom)))

#check (IsPresentation.ofProIso :
  ∀ (f : X ⟶ Y)
    (K : Dᵇ[SheafOfModules.isCoherent X.obj.left.ringCatSheaf])
    {A B : PNatInverseSystem
      Dᵇ[SheafOfModules.isCoherent Y.obj.left.ringCatSheaf]},
    IsPresentation f K A →
      (boundedProObject A ≅ boundedProObject B) → IsPresentation f K B)

end AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport
