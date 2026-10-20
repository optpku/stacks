module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.DeligneSystem.ExtensionByZero
public import ReasLib.CategoryTheory.Pro.Presentation

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open DerivedCategory.Bounded.CohomologyIn
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe v

namespace AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem

variable {X Y : Scheme.{v}} (f : X ⟶ Y)
variable [IsNoetherian X] [IsNoetherian Y] [IsProper f]

/-- The positive bounded coherent tower obtained by applying proper derived pushforward to each
stage of a Deligne system. -/
noncomputable def properPushforwardTower
    {U : Scheme.{v}} {j : U ⟶ X} [IsNoetherian U] [IsOpenImmersion j]
    (S : DeligneSystem j) :
    PNatInverseSystem Dᵇ[SheafOfModules.isCoherent Y.ringCatSheaf] :=
  S.boundedTower ⋙ AlgebraicGeometry.Scheme.ModuleDerived.properPushforward f

/-- A comparison isomorphism between the Deligne extension of a proper pushforward and the
pro-limit of the pushed Deligne tower is compatible with restriction to the constant object
valued at that proper pushforward if it identifies morphisms out of the pro-limit with morphisms
out of the restricted value. -/
def RestrictsToConstantProperPushforward
    {V : Y.Opens} [IsNoetherian V] [IsNoetherian (f ⁻¹ᵁ V)]
    (K : Dᵇ[SheafOfModules.isCoherent (f ⁻¹ᵁ V).toScheme.ringCatSheaf])
    (e :
      (extensionByZero V.ι).obj
          ((AlgebraicGeometry.Scheme.ModuleDerived.properPushforward (f ∣_ V)).obj K) ≅
        (CategoryTheory.Pro.lim
            (C := Dᵇ[SheafOfModules.isCoherent Y.ringCatSheaf]) (OrderDual ℕ+)).obj
          (properPushforwardTower f (extension (f ⁻¹ᵁ V).ι K))) : Prop :=
  ∀ (L : Dᵇ[SheafOfModules.isCoherent Y.ringCatSheaf]),
    Function.Bijective
      (fun (β :
          (CategoryTheory.Pro.lim
              (C := Dᵇ[SheafOfModules.isCoherent Y.ringCatSheaf]) (OrderDual ℕ+)).obj
            (properPushforwardTower f (extension (f ⁻¹ᵁ V).ι K)) ⟶
            CategoryTheory.Pro.yoneda.obj L) =>
        extensionByZeroHomMap V.ι
          ((AlgebraicGeometry.Scheme.ModuleDerived.properPushforward (f ∣_ V)).obj K) L
          (e.hom ≫ β))

/-- There is a unique pro-isomorphism between the Deligne extension of a proper pushforward and
the pro-limit of the stagewise proper pushforward of a Deligne extension, compatible with
restriction to the constant proper pushforward. -/
theorem existsUnique_iso_extensionByZero_properPushforwardLim
    {V : Y.Opens} [IsNoetherian V] [IsNoetherian (f ⁻¹ᵁ V)]
    (K : Dᵇ[SheafOfModules.isCoherent (f ⁻¹ᵁ V).toScheme.ringCatSheaf]) :
    ∃! e :
      (extensionByZero V.ι).obj
          ((AlgebraicGeometry.Scheme.ModuleDerived.properPushforward (f ∣_ V)).obj K) ≅
        (CategoryTheory.Pro.lim
            (C := Dᵇ[SheafOfModules.isCoherent Y.ringCatSheaf]) (OrderDual ℕ+)).obj
          (properPushforwardTower f (extension (f ⁻¹ᵁ V).ι K)),
      RestrictsToConstantProperPushforward f K e := sorry

/-- The unique restriction-compatible comparison isomorphism between the Deligne extension of a
proper pushforward and the pro-limit of the pushed Deligne tower. -/
noncomputable def iso_extensionByZero_properPushforwardLim
    {V : Y.Opens} [IsNoetherian V] [IsNoetherian (f ⁻¹ᵁ V)]
    (K : Dᵇ[SheafOfModules.isCoherent (f ⁻¹ᵁ V).toScheme.ringCatSheaf]) :
    (extensionByZero V.ι).obj
        ((AlgebraicGeometry.Scheme.ModuleDerived.properPushforward (f ∣_ V)).obj K) ≅
      (CategoryTheory.Pro.lim
          (C := Dᵇ[SheafOfModules.isCoherent Y.ringCatSheaf]) (OrderDual ℕ+)).obj
        (properPushforwardTower f (extension (f ⁻¹ᵁ V).ι K)) :=
  Classical.choose (existsUnique_iso_extensionByZero_properPushforwardLim f K)

/-- The functor sending a bounded coherent complex on the preimage of an open of `Y` to the
pro-object presented by the stagewise proper pushforward of its chosen Deligne extension. -/
noncomputable def properPushforwardLim
    {V : Y.Opens} [IsNoetherian V] [IsNoetherian (f ⁻¹ᵁ V)] :
    Dᵇ[SheafOfModules.isCoherent (f ⁻¹ᵁ V).toScheme.ringCatSheaf] ⥤
      CategoryTheory.Pro Dᵇ[SheafOfModules.isCoherent Y.ringCatSheaf] where
  obj K :=
    (CategoryTheory.Pro.lim
        (C := Dᵇ[SheafOfModules.isCoherent Y.ringCatSheaf]) (OrderDual ℕ+)).obj
      (properPushforwardTower f (extension (f ⁻¹ᵁ V).ι K))
  map {K L} g :=
    (iso_extensionByZero_properPushforwardLim f K).inv ≫
      (extensionByZero V.ι).map
        ((AlgebraicGeometry.Scheme.ModuleDerived.properPushforward (f ∣_ V)).map g) ≫
      (iso_extensionByZero_properPushforwardLim f L).hom
  map_id _ := sorry
  map_comp _ _ := sorry

/-- Canonical natural isomorphism identifying proper pushforward after extension by zero along
the open immersion of `V` with extension by zero after proper pushforward, realized on the
Deligne presentation by the pro-limit of the stagewise proper-pushed-forward tower. -/
noncomputable def extensionByZero_pushforwardIso
    {V : Y.Opens} [IsNoetherian V] [IsNoetherian (f ⁻¹ᵁ V)] :
    AlgebraicGeometry.Scheme.ModuleDerived.properPushforward (f ∣_ V) ⋙
        extensionByZero V.ι ≅
      properPushforwardLim f (V := V) where
  hom :=
    { app := fun K => (iso_extensionByZero_properPushforwardLim f K).hom
      naturality := fun _ _ _ => sorry }
  inv :=
    { app := fun K => (iso_extensionByZero_properPushforwardLim f K).inv
      naturality := fun _ _ _ => sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem
