module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.FixedInterior
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.DeligneSystem.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.DeligneSystem.Restriction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Adjunction

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open DerivedCategory.Bounded.CohomologyIn
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe v

namespace AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem

section ProperPushforwardAlong

variable {X Y U : Scheme.{v}} (f : X ⟶ Y) (j' : U ⟶ X)
variable [IsNoetherian X] [IsNoetherian Y] [IsNoetherian U]
variable [IsProper f] [IsOpenImmersion j']

/-- Scheme module pullback and pushforward form an absolute derived adjunction pair. -/
theorem properPushforwardAlong_derivedPair :
    RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom f.toShHom) := sorry

/-- Restrict a pushed-forward stage back to the fixed interior, using the
derived adjunction counit and the given Deligne restriction identification.
This map is fixed by geometry, independently of a proposed pro-isomorphism. -/
noncomputable def properPushforwardAlongStageCounit
    (j : U ⟶ Y) [IsOpenImmersion j] (htriangle : j' ≫ f = j)
    (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]) (n : OrderDual ℕ+) :
    (ambient (SheafOfModules.isCoherent U.ringCatSheaf)).obj
        ((restriction j).obj ((properPushforwardTower f (extension j' K)).obj n)) ⟶
      (ambient (SheafOfModules.isCoherent U.ringCatSheaf)).obj K :=
  -- Local instance justification (proof-local temporary data): construct the canonical
  -- derived counit using its absolute-derived pair certificate.
  letI := properPushforwardAlong_derivedPair f
  let S := extension j' K
  let E := (ambient (SheafOfModules.isCoherent X.ringCatSheaf)).obj ((boundedTower j' S).obj n)
  (restrictionAmbientIso j).hom.app ((properPushforwardTower f S).obj n) ≫
    (RingedSpace.modulePullbackDerived j.toShHom).map
      ((AlgebraicGeometry.Scheme.ModuleDerived.properPushforward.ambientIso f).hom.app
        ((boundedTower j' S).obj n)) ≫
    (eqToIso (congrArg (fun q : U ⟶ Y ↦ RingedSpace.modulePullbackDerived q.toShHom)
      htriangle)).inv.app ((RingedSpace.moduleDerivedPushforward f.toShHom).obj E) ≫
    (RingedSpace.modulePullbackDerived.compIso j'.toShHom f.toShHom
      (RingedSpace.modulePullbackDerived.compComparison_isIso j'.toShHom f.toShHom)).inv.app
        ((RingedSpace.moduleDerivedPushforward f.toShHom).obj E) ≫
    (RingedSpace.modulePullbackDerived j'.toShHom).map
      ((RingedSpace.modulePullbackDerivedPushforwardAdjunction f.toShHom).counit.app E) ≫
    (RingedSpace.modulePullbackDerived j'.toShHom).map
      ((boundedTowerAmbientIso j' S).hom.app n) ≫
    S.restrictionIso.hom.app n ≫
    (ambient (SheafOfModules.isCoherent U.ringCatSheaf)).map (eqToHom (extension_value j' K))

/-- A comparison isomorphism between Deligne extension by zero along an open immersion `j`
and the pro-limit of the stagewise proper pushforward of a Deligne extension along `j'` is
compatible with restriction if every stage component, followed by the canonical interior
counit, is the identity of `K`. Mere bijectivity does not characterize this map. -/
def RestrictsToConstantProperPushforwardAlong
    (j : U ⟶ Y) [IsOpenImmersion j] (htriangle : j' ≫ f = j)
    (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf])
    (e :
      (extensionByZero j).obj K ≅
        (CategoryTheory.Pro.lim
            (C := Dᵇ[SheafOfModules.isCoherent Y.ringCatSheaf]) (OrderDual ℕ+)).obj
          (properPushforwardTower f (extension j' K))) : Prop :=
  ∀ n : OrderDual ℕ+,
    (ambient (SheafOfModules.isCoherent U.ringCatSheaf)).map
      ((extensionValueIso j (extension j) (extension_value j) K).inv ≫
        (boundedHomColimitToRestriction j (extension j K)).app
          ((properPushforwardTower f (extension j' K)).obj n)
          ((Pro.homColimit.homEquiv (boundedTower j (extension j K))
            (properPushforwardTower f (extension j' K)) e.hom).app
              ((properPushforwardTower f (extension j' K)).obj n)
              ((colimit.ι ((properPushforwardTower f (extension j' K)).op ⋙ coyoneda)
                (Opposite.op n)).app ((properPushforwardTower f (extension j' K)).obj n)
                  (𝟙 _)))) ≫ properPushforwardAlongStageCounit f j' j htriangle K n = 𝟙 _

/-- There is a unique restriction-compatible pro-isomorphism between Deligne extension by zero
along `j` and the pro-limit of the stagewise proper pushforward of a Deligne extension along
`j'`. -/
theorem existsUnique_iso_extensionByZero_properPushforwardLimAlong
    (j : U ⟶ Y) [IsOpenImmersion j] (htriangle : j' ≫ f = j)
    (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]) :
    ∃! e :
      (extensionByZero j).obj K ≅
        (CategoryTheory.Pro.lim
            (C := Dᵇ[SheafOfModules.isCoherent Y.ringCatSheaf]) (OrderDual ℕ+)).obj
          (properPushforwardTower f (extension j' K)),
      RestrictsToConstantProperPushforwardAlong f j' j htriangle K e := sorry

/-- The unique restriction-compatible comparison isomorphism between Deligne extension by zero
along `j` and the pro-limit of the pushed Deligne tower along `j'`. -/
noncomputable def iso_extensionByZero_properPushforwardLimAlong
    (j : U ⟶ Y) [IsOpenImmersion j] (htriangle : j' ≫ f = j)
    (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]) :
    (extensionByZero j).obj K ≅
      (CategoryTheory.Pro.lim
          (C := Dᵇ[SheafOfModules.isCoherent Y.ringCatSheaf]) (OrderDual ℕ+)).obj
        (properPushforwardTower f (extension j' K)) :=
  Classical.choose (existsUnique_iso_extensionByZero_properPushforwardLimAlong f j' j htriangle K)

/-- The selected comparison restricts to the identity through the actual geometric counit. -/
theorem iso_extensionByZero_properPushforwardLimAlong_spec
    (j : U ⟶ Y) [IsOpenImmersion j] (htriangle : j' ≫ f = j)
    (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]) :
    RestrictsToConstantProperPushforwardAlong f j' j htriangle K
      (iso_extensionByZero_properPushforwardLimAlong f j' j htriangle K) :=
  (Classical.choose_spec
    (existsUnique_iso_extensionByZero_properPushforwardLimAlong f j' j htriangle K)).1

/-- Any comparison satisfying the same interior identity is the selected comparison. -/
theorem iso_extensionByZero_properPushforwardLimAlong_unique
    (j : U ⟶ Y) [IsOpenImmersion j] (htriangle : j' ≫ f = j)
    (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf])
    (e : (extensionByZero j).obj K ≅
      (CategoryTheory.Pro.lim
        (C := Dᵇ[SheafOfModules.isCoherent Y.ringCatSheaf]) (OrderDual ℕ+)).obj
          (properPushforwardTower f (extension j' K)))
    (he : RestrictsToConstantProperPushforwardAlong f j' j htriangle K e) :
    e = iso_extensionByZero_properPushforwardLimAlong f j' j htriangle K :=
  (Classical.choose_spec
    (existsUnique_iso_extensionByZero_properPushforwardLimAlong f j' j htriangle K)).2 e he

/-- The functor sending a bounded coherent complex on `U` to the pro-object presented by the
stagewise proper pushforward of its chosen Deligne extension along `j'`. -/
noncomputable def properPushforwardLimAlong
    [h_open : IsOpenImmersion (j' ≫ f)] :
    Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf] ⥤
      CategoryTheory.Pro Dᵇ[SheafOfModules.isCoherent Y.ringCatSheaf] where
  obj K :=
    (CategoryTheory.Pro.lim
        (C := Dᵇ[SheafOfModules.isCoherent Y.ringCatSheaf]) (OrderDual ℕ+)).obj
      (properPushforwardTower f (extension j' K))
  map {K L} g :=
    (iso_extensionByZero_properPushforwardLimAlong f j' (j' ≫ f) rfl K).inv ≫
      (extensionByZero (j' ≫ f)).map g ≫
      (iso_extensionByZero_properPushforwardLimAlong f j' (j' ≫ f) rfl L).hom
  map_id _ := sorry
  map_comp _ _ := sorry

end ProperPushforwardAlong

variable {X U : Scheme.{v}}

/-- The compactification triangle identifies the original open immersion with the composite of
the interior immersion and the proper structure morphism. -/
theorem isOpenImmersion_compactification_comp
    {S : Scheme.{v}} {X : Over S} (hX : IsOpenImmersion X.hom) (P : Compactification.Of S X) :
    IsOpenImmersion (Compactification.Of.ι P ≫ P.obj.right.hom) :=
  (Over.w P.obj.hom).symm ▸ hX

/-- Canonical natural isomorphism identifying Deligne extension by zero along an open immersion
with Deligne extension by zero along the interior of a compactification, followed by the
pro-limit of the stagewise proper pushforward of that Deligne tower. -/
noncomputable def extensionByZero_compactificationIso
    {X U : Scheme.{v}} (j : U ⟶ X) [IsNoetherian X] [IsNoetherian U] [IsOpenImmersion j]
    (P : Compactification.Of X (Over.mk j)) :
    extensionByZero j ≅
      @properPushforwardLimAlong P.obj.right.left X U P.obj.right.hom
        (Compactification.Of.ι P)
        (Compactification.Of.instAmbientIsNoetherian P) ‹_› ‹_›
        (Compactification.Of.instIsProper X (Over.mk j) P)
        (Compactification.Of.instIsOpenImmersion X (Over.mk j) P)
        (isOpenImmersion_compactification_comp ‹IsOpenImmersion j› P) where
  hom :=
    { app := fun K =>
        @iso_extensionByZero_properPushforwardLimAlong P.obj.right.left X U
          P.obj.right.hom (Compactification.Of.ι P)
          (Compactification.Of.instAmbientIsNoetherian P) ‹_› ‹_›
          (Compactification.Of.instIsProper X (Over.mk j) P)
          (Compactification.Of.instIsOpenImmersion X (Over.mk j) P)
          j ‹_› (Over.w P.obj.hom) K |>.hom
      naturality := fun _ _ _ => sorry }
  inv :=
    { app := fun K =>
        @iso_extensionByZero_properPushforwardLimAlong P.obj.right.left X U
          P.obj.right.hom (Compactification.Of.ι P)
          (Compactification.Of.instAmbientIsNoetherian P) ‹_› ‹_›
          (Compactification.Of.instIsProper X (Over.mk j) P)
          (Compactification.Of.instIsOpenImmersion X (Over.mk j) P)
          j ‹_› (Over.w P.obj.hom) K |>.inv
      naturality := fun _ _ _ => sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem
