module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Dualizing.EtaleLocal

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open AlgebraicGeometry.Scheme.DerivedQCoh (SmallEtale epsilonStar)
open RingedSite.Hom

universe u

#check (AlgebraicGeometry.AlgebraicSpace.schemeEtaleRingedHom_modulePushforward_preservesFiniteLimits :
    ∀ {S : Scheme.{u}} (U : Over S),
    PreservesFiniteLimits (schemeEtaleRingedHom U).modulePushforward.{u})

#check (AlgebraicGeometry.AlgebraicSpace.schemeEtaleRingedHom_modulePushforward_preservesFiniteColimits :
    ∀ {S : Scheme.{u}} (U : Over S),
    PreservesFiniteColimits (schemeEtaleRingedHom U).modulePushforward.{u})

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.toEtaleDerived :
    ∀ {S : Scheme.{u}} (U : Over S),
    ModuleDerived (ofOver U) ⥤
      DerivedCategory (RingedSite.ModuleCat.{u} (Scheme.Etale.Small.ringedSite U.left)))

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.toEtaleDerived_eq :
    ∀ {S : Scheme.{u}} (U : Over S),
    toEtaleDerived U =
      (schemeEtaleRingedHom U).modulePushforward.{u}.mapDerivedCategory)

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.toEtaleDerived_obj :
    ∀ {S : Scheme.{u}} (U : Over S)
    (K : ModuleDerived (ofOver U)),
    (toEtaleDerived U).obj K =
      ((schemeEtaleRingedHom U).modulePushforward.{u}.mapDerivedCategory).obj K)

#check (AlgebraicGeometry.AlgebraicSpace.isLocallyNoetherian_left_of_etaleChart :
    ∀ {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsLocallyNoetherian X] {U : Over S}
    (φ : ofOver U ⟶ X) [Etale φ],
    AlgebraicGeometry.IsLocallyNoetherian U.left)

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.isDualizingOnScheme :
    ∀ {S : Scheme.{u}} (U : Over S)
    [AlgebraicGeometry.IsLocallyNoetherian U.left]
    (K : ModuleDerived (ofOver U)),
    Prop)

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.isDualizingOnScheme_iff :
    ∀ {S : Scheme.{u}} (U : Over S)
    [AlgebraicGeometry.IsLocallyNoetherian U.left]
    (K : ModuleDerived (ofOver U)),
    isDualizingOnScheme U K ↔
      ∃ ω : Scheme.DerivedQCoh U.left,
        Scheme.IsDualizingComplex ω.obj ∧
          IsIsomorphic ((toEtaleDerived U).obj K)
            ((SmallEtale.inclusion U.left).obj
              ((epsilonStar U.left).obj ω)))

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.isDualizingOnScheme.of :
    ∀ {S : Scheme.{u}} {U : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian U.left]
    {K : ModuleDerived (ofOver U)} (ω : Scheme.DerivedQCoh U.left)
    (hω : Scheme.IsDualizingComplex ω.obj)
    (hiso : IsIsomorphic ((toEtaleDerived U).obj K)
      ((SmallEtale.inclusion U.left).obj
        ((epsilonStar U.left).obj ω))),
    isDualizingOnScheme U K)

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.isDualizingOnScheme.spec :
    ∀ {S : Scheme.{u}} {U : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian U.left]
    {K : ModuleDerived (ofOver U)} (h : isDualizingOnScheme U K),
    ∃ ω : Scheme.DerivedQCoh U.left,
      Scheme.IsDualizingComplex ω.obj ∧
        IsIsomorphic ((toEtaleDerived U).obj K)
          ((SmallEtale.inclusion U.left).obj
            ((epsilonStar U.left).obj ω)))

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.forallEtaleScheme :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] (K : DerivedQCoh X),
    Prop)

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.forallEtaleScheme_iff :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] (K : DerivedQCoh X),
    forallEtaleScheme K ↔
      ∀ (U : Over S) (φ : ofOver U ⟶ X) [Etale φ]
        [AlgebraicGeometry.IsLocallyNoetherian U.left],
        isDualizingOnScheme U
          ((ModuleDerived.pullback φ).obj ((inclusion X).obj K)))

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.forallEtaleScheme.of :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
    {K : DerivedQCoh X}
    (h : ∀ (U : Over S) (φ : ofOver U ⟶ X) [Etale φ]
      [AlgebraicGeometry.IsLocallyNoetherian U.left],
      isDualizingOnScheme U
        ((ModuleDerived.pullback φ).obj ((inclusion X).obj K))),
    forallEtaleScheme K)

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.forallEtaleScheme.spec :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
    {K : DerivedQCoh X} (h : forallEtaleScheme K),
    ∀ (U : Over S) (φ : ofOver U ⟶ X) [Etale φ]
      [AlgebraicGeometry.IsLocallyNoetherian U.left],
      isDualizingOnScheme U
        ((ModuleDerived.pullback φ).obj ((inclusion X).obj K)))

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.forallEtaleScheme.apply :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
    {K : DerivedQCoh X} (h : forallEtaleScheme K) {U : Over S}
    (φ : ofOver U ⟶ X) [Etale φ]
    [AlgebraicGeometry.IsLocallyNoetherian U.left],
    isDualizingOnScheme U
      ((ModuleDerived.pullback φ).obj ((inclusion X).obj K)))

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.existsSurjectiveEtaleScheme :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] (K : DerivedQCoh X),
    Prop)

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.existsSurjectiveEtaleScheme_iff :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] (K : DerivedQCoh X),
    existsSurjectiveEtaleScheme K ↔
      ∃ (U : Over S) (φ : ofOver U ⟶ X) (hφ : Etale φ) (_ : Surjective φ)
        (_ : AlgebraicGeometry.IsLocallyNoetherian U.left),
        isDualizingOnScheme U
          ((ModuleDerived.pullback φ).obj ((inclusion X).obj K)))

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.existsSurjectiveEtaleScheme.of :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
    {K : DerivedQCoh X} {U : Over S} (φ : ofOver U ⟶ X) [Etale φ] [Surjective φ]
    [AlgebraicGeometry.IsLocallyNoetherian U.left]
    (hK : isDualizingOnScheme U
      ((ModuleDerived.pullback φ).obj ((inclusion X).obj K))),
    existsSurjectiveEtaleScheme K)

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.existsSurjectiveEtaleScheme.spec :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
    {K : DerivedQCoh X} (h : existsSurjectiveEtaleScheme K),
    ∃ (U : Over S) (φ : ofOver U ⟶ X) (hφ : Etale φ) (_ : Surjective φ)
      (_ : AlgebraicGeometry.IsLocallyNoetherian U.left),
      isDualizingOnScheme U
        ((ModuleDerived.pullback φ).obj ((inclusion X).obj K)))
